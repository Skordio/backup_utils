#!/usr/bin/env python3
"""Back up a removable drive to a timestamped folder.

Python port of backup.ps1, with selectable drive letter, adjustable
verbosity, a progress bar pinned to the bottom of the terminal, graceful
double-Ctrl+C handling, default logging, and resume of interrupted backups.

Standard library only -- no third-party packages required.
"""

import argparse
import ctypes
import json
import os
import shutil
import signal
import string
import sys
import time
import zipfile
from datetime import datetime
from pathlib import Path

DESTINATION_BASE = Path(r"C:\Users\skord\Backups\Flipper")
MARKER_NAME = ".backup_incomplete.json"
LOG_NAME = "backup.log"
DOUBLE_PRESS_SECONDS = 5


# --------------------------------------------------------------------------- #
# Terminal control
# --------------------------------------------------------------------------- #
def enable_vt_mode():
    """Enable ANSI escape processing on the Windows console.

    The progress display writes to stderr, so the return value reflects whether
    *stderr* can use VT sequences -- a redirected stdout must not force the
    space-padding fallback on a VT-capable stderr. Returns True if erase-line
    sequences are usable, else False so callers fall back to space-padding.
    """
    if os.name != "nt":
        return True  # POSIX terminals handle ANSI natively.
    ENABLE_VT = 0x0004
    kernel32 = ctypes.windll.kernel32
    stderr_ok = False
    for std_handle in (-11, -12):  # STD_OUTPUT_HANDLE, STD_ERROR_HANDLE
        handle = kernel32.GetStdHandle(std_handle)
        mode = ctypes.c_uint32()
        if not kernel32.GetConsoleMode(handle, ctypes.byref(mode)):
            continue
        enabled = bool(kernel32.SetConsoleMode(handle, mode.value | ENABLE_VT))
        if std_handle == -12:  # STD_ERROR_HANDLE -- the stream we draw on
            stderr_ok = enabled
    return stderr_ok


# --------------------------------------------------------------------------- #
# Drive discovery / validation
# --------------------------------------------------------------------------- #
def available_drives():
    """Return a list of drive letters (e.g. ['C', 'D']) currently present."""
    if os.name == "nt":
        bitmask = ctypes.windll.kernel32.GetLogicalDrives()
        return [
            letter
            for i, letter in enumerate(string.ascii_uppercase)
            if bitmask & (1 << i)
        ]
    # Non-Windows fallback: just check common mount roots.
    return [d for d in string.ascii_uppercase if Path(f"{d}:\\").exists()]


def volume_label(letter):
    """Return the filesystem label for a drive letter, or '' if unavailable."""
    root = f"{letter}:\\"
    if os.name != "nt":
        return ""
    buf = ctypes.create_unicode_buffer(1024)
    fs_buf = ctypes.create_unicode_buffer(1024)
    ok = ctypes.windll.kernel32.GetVolumeInformationW(
        ctypes.c_wchar_p(root),
        buf,
        ctypes.sizeof(buf),
        None,
        None,
        None,
        fs_buf,
        ctypes.sizeof(fs_buf),
    )
    return buf.value if ok else ""


def resolve_source(value):
    """Turn a user-supplied source string into a Path.

    A bare drive letter -- 'D', 'd', 'D:', 'D:\\' or 'D:/' -- expands to the
    whole drive root ('D:\\'), preserving the original drive-letter behavior.
    Anything else is treated as a literal file or directory path.
    """
    v = value.strip().strip('"').strip("'")
    core = v.rstrip("\\/")
    if core.endswith(":"):
        core = core[:-1]
    if len(core) == 1 and core.isalpha():
        return Path(f"{core.upper()}:\\")
    return Path(v)


def describe_source(source):
    """Human-readable label for a source: volume label for a drive root,
    otherwise the path itself."""
    s = str(source)
    if len(s) == 3 and s[1] == ":" and s[2] == "\\":  # e.g. 'D:\'
        label = volume_label(s[0])
        return f"{label or '(no label)'} ({s})"
    return s


def prompt_for_source(preferred=None):
    """Ask for a drive letter or a path to back up; validate it exists."""
    drives = available_drives()
    while True:
        if preferred:
            raw = preferred
            preferred = None  # only auto-use the CLI value once
        else:
            print("\nAvailable drives:")
            for d in drives:
                label = volume_label(d)
                shown = f" ({label})" if label else ""
                print(f"  {d}:\\{shown}")
            raw = input(
                "\nEnter a drive letter (e.g. D) or a path to back up: "
            ).strip()

        if not raw:
            print("  Please enter a drive letter or a path.")
            continue
        source = resolve_source(raw)
        if not source.exists():
            print(f"  '{source}' does not exist or is not accessible.")
            continue
        return source


# --------------------------------------------------------------------------- #
# File enumeration
# --------------------------------------------------------------------------- #
def gather_files(source):
    """Walk the source, returning (files, total_bytes).

    files is a list of (src_path, relative_path) tuples. A single-file source
    yields one entry whose relative path is just the file name.
    """
    files = []
    total = 0
    if source.is_file():
        try:
            total = source.stat().st_size
        except OSError:
            total = 0
        return [(source, Path(source.name))], total
    for root, _dirs, names in os.walk(source):
        for name in names:
            src = Path(root) / name
            try:
                size = src.stat().st_size
            except OSError:
                size = 0
            files.append((src, src.relative_to(source)))
            total += size
    return files, total


def human_bytes(n):
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if n < 1024 or unit == "TB":
            return f"{n:.1f}{unit}"
        n /= 1024


# --------------------------------------------------------------------------- #
# Progress display (bar pinned to the bottom, log lines scroll above)
# --------------------------------------------------------------------------- #
class ProgressDisplay:
    """Owns the live output region so the bar and the file list never desync.

    All live-region output -- the bar plus any per-file or warning lines --
    goes through this one object on a single stream, so "print above the bar"
    stays consistent. On a non-TTY stream it degrades to plain lines plus
    percentage milestones, with no escape sequences.
    """

    def __init__(self, total_bytes, verbosity, stream=None, use_vt=True):
        self.total = total_bytes
        self.verbosity = verbosity
        self.stream = stream if stream is not None else sys.stderr
        self.is_tty = bool(getattr(self.stream, "isatty", lambda: False)())
        self.use_vt = use_vt
        self.max_bar = 34
        self.done = 0
        self.last_name = ""
        self.start = time.time()
        self._next_milestone = 10  # for non-TTY percentage reporting

    # -- internals ---------------------------------------------------------- #
    def _term_width(self):
        return shutil.get_terminal_size((80, 24)).columns

    def _clear_seq(self):
        if self.use_vt:
            return "\r\033[2K"
        return "\r" + " " * (self._term_width() - 1) + "\r"

    def _render_bar(self):
        term = self._term_width()
        frac = (self.done / self.total) if self.total else 1.0
        frac = min(frac, 1.0)
        elapsed = time.time() - self.start
        rate = self.done / elapsed if elapsed > 0 else 0
        eta = (self.total - self.done) / rate if rate > 0 else 0
        suffix = (
            f" {frac * 100:5.1f}%  "
            f"{human_bytes(self.done)}/{human_bytes(self.total)}  "
            f"ETA {int(eta):4d}s"
        )
        # Size the bar to the terminal (2 cols for the brackets) so the whole
        # line fits and can't wrap.
        bar_width = max(10, min(self.max_bar, term - len(suffix) - 2))
        filled = int(bar_width * frac)
        bar = "#" * filled + "-" * (bar_width - filled)
        line = f"[{bar}]{suffix}"
        # Only verbosity 0 appends the in-flight filename (no scrolling list).
        if self.verbosity == 0 and self.last_name:
            avail = term - len(line) - 3
            if avail >= 8:
                name = self.last_name
                if len(name) > avail:
                    name = "..." + name[-(avail - 3):]
                line += f"  {name}"
        # Hard clamp: never exceed the terminal width, or the line wraps and the
        # single-line redraw corrupts.
        return line[:term - 1]

    # -- public API --------------------------------------------------------- #
    # Each method emits its escape sequence + text in a single write() so a
    # SIGINT landing mid-render can't interleave a half-drawn line.
    def update(self, done, name=None):
        self.done = done
        if name is not None:
            self.last_name = name
        if self.is_tty:
            self.stream.write(self._clear_seq() + self._render_bar())
            self.stream.flush()
        else:
            pct = (done / self.total * 100) if self.total else 100
            while pct >= self._next_milestone and self._next_milestone <= 100:
                self.stream.write(f"  ... {self._next_milestone}%\n")
                self._next_milestone += 10
            self.stream.flush()

    def log(self, msg):
        """Print a line above the bar (or plainly on a non-TTY)."""
        if self.is_tty:
            self.stream.write(self._clear_seq() + msg + "\n" + self._render_bar())
            self.stream.flush()
        else:
            self.stream.write(msg + "\n")
            self.stream.flush()

    def close(self, completed=True):
        """Draw the final bar. Only a completed run is forced to 100%; an
        interrupted or partially-failed run keeps its true position."""
        if not self.is_tty:
            return
        if completed:
            self.done = self.total
        self.stream.write(self._clear_seq() + self._render_bar() + "\n")
        self.stream.flush()


# --------------------------------------------------------------------------- #
# Logging
# --------------------------------------------------------------------------- #
def open_log(log_path, append=False):
    """Open the log file, returning a file handle (or None on failure)."""
    if log_path is None:
        return None
    try:
        log_path.parent.mkdir(parents=True, exist_ok=True)
        return open(log_path, "a" if append else "w", encoding="utf-8")
    except OSError as exc:
        print(f"  ! Could not open log file {log_path}: {exc}")
        return None


def log_line(handle, message):
    """Write a timestamped line to the log, if logging is enabled."""
    if handle is None:
        return
    stamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    handle.write(f"{stamp}  {message}\n")
    handle.flush()


# --------------------------------------------------------------------------- #
# Resume marker
# --------------------------------------------------------------------------- #
def write_marker(destination, source, label, started, total_files, total_bytes):
    """Drop a marker that flags this backup folder as incomplete."""
    data = {
        "source": str(source),
        "label": label,
        "started": started,
        "total_files": total_files,
        "total_bytes": total_bytes,
    }
    try:
        (destination / MARKER_NAME).write_text(json.dumps(data), encoding="utf-8")
    except OSError:
        pass  # A missing marker only costs us the resume hint, not the backup.


def clear_marker(destination):
    """Remove the incomplete-marker; its absence means the backup finished."""
    try:
        (destination / MARKER_NAME).unlink()
    except OSError:
        pass


def find_incomplete(source):
    """Return the most recent incomplete backup folder for a source, or None."""
    if not DESTINATION_BASE.exists():
        return None
    key = str(source)
    candidates = []
    for child in DESTINATION_BASE.iterdir():
        marker = child / MARKER_NAME
        if not marker.is_file():
            continue
        try:
            data = json.loads(marker.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            continue
        if data.get("source") == key:
            candidates.append((child.name, child, data))
    if not candidates:
        return None
    # Folder names are sortable timestamps (yyyyMMdd_HHmmss); newest wins.
    candidates.sort(key=lambda c: c[0])
    return candidates[-1]


# --------------------------------------------------------------------------- #
# Archiving
# --------------------------------------------------------------------------- #
def zip_backup(destination, verbosity, use_vt, compress=True):
    """Compress everything in ``destination`` into a sibling .zip.

    Returns (archive_path, ok). ``ok`` is False if the archive could not be
    written or fails verification, in which case the caller must keep the
    uncompressed folder.
    """
    archive = destination.with_name(destination.name + ".zip")

    entries = []
    total = 0
    for root, _dirs, names in os.walk(destination):
        for name in names:
            p = Path(root) / name
            try:
                total += p.stat().st_size
            except OSError:
                pass
            entries.append(p)

    print(f"\nCompressing {len(entries)} files into {archive.name} ...")
    method = zipfile.ZIP_DEFLATED if compress else zipfile.ZIP_STORED
    display = ProgressDisplay(total, verbosity, use_vt=use_vt)
    done = 0
    written = 0
    try:
        with zipfile.ZipFile(archive, "w", method, allowZip64=True) as zf:
            for p in entries:
                rel = p.relative_to(destination)
                try:
                    zf.write(p, str(rel))
                    written += 1
                    done += p.stat().st_size
                    if verbosity >= 2:
                        display.log(f"  ZIP   {rel}")
                except OSError as exc:
                    display.log(f"  ! zip failed: {rel} -- {exc}")
                display.update(done, name=str(rel))
        display.close(completed=True)
    except OSError as exc:
        display.close(completed=False)
        print(f"  ! Could not create archive: {exc}")
        return archive, False

    # Verify before the caller is allowed to delete the source folder.
    try:
        with zipfile.ZipFile(archive) as zf:
            bad = zf.testzip()
            count = len(zf.namelist())
    except (OSError, zipfile.BadZipFile) as exc:
        print(f"  ! Archive verification failed: {exc}")
        return archive, False
    if bad is not None or count != written:
        print(f"  ! Archive verification failed "
              f"(corrupt entry={bad}, {count} of {written} entries).")
        return archive, False

    print(f"  Archived and verified: {archive} "
          f"({human_bytes(archive.stat().st_size)}, {written} files)")
    return archive, True


# --------------------------------------------------------------------------- #
# Backup
# --------------------------------------------------------------------------- #
def run_backup(source, verbosity, assume_yes, log_path, resume_choice,
               use_vt=True, make_zip=False, zip_keep=False, zip_compress=True):
    label = describe_source(source)

    # ------------------------------------------------------------------ #
    # Decide destination: fresh timestamped folder, or resume an existing one.
    # ------------------------------------------------------------------ #
    destination = None
    resuming = False
    if resume_choice == "NONE":
        pass  # forced fresh
    elif isinstance(resume_choice, Path):
        destination = resume_choice
        resuming = True
    else:  # "AUTO" (bare --resume) or "PROMPT" (default: ask if one is found)
        found = find_incomplete(source)
        if found:
            name, folder, data = found
            done_hint = data.get("total_files", "?")
            # --yes implies unattended: auto-resume rather than block on input.
            if resume_choice == "AUTO" or assume_yes:
                destination, resuming = folder, True
                if assume_yes and resume_choice != "AUTO":
                    print(f"\n--yes: auto-resuming interrupted backup from {name}.")
            else:
                print(f"\nFound an interrupted backup from {name} "
                      f"({label}, {done_hint} files planned).")
                ans = input("Resume it? [Y/n]: ").strip().lower()
                if ans in ("", "y", "yes"):
                    destination, resuming = folder, True

    if destination is None:
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        destination = DESTINATION_BASE / timestamp

    # Default log lives inside the backup folder itself.
    if log_path == "DEFAULT":
        log_path = destination / LOG_NAME

    print(f"\n{'Resuming' if resuming else 'Backing up'} source: {label}")
    print(f"Destination:      {destination}")
    if log_path:
        print(f"Log:              {log_path}")

    if not assume_yes:
        if input("Press Enter to confirm and continue (or 'n' to abort): ").strip().lower() == "n":
            print("Aborted.")
            return 1

    print("\nScanning files...")
    files, total_bytes = gather_files(source)
    file_count = len(files)
    if file_count == 0:
        print("Nothing to copy -- the source is empty or unreadable.")
        return 0
    print(f"Found {file_count} files, {human_bytes(total_bytes)} total.\n")

    destination.mkdir(parents=True, exist_ok=True)
    started = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    write_marker(destination, source, label, started, file_count, total_bytes)

    log = open_log(log_path, append=resuming)
    log_line(log, f"{'Resumed' if resuming else 'Backup started'}: "
                  f"{label} -> {destination}")
    log_line(log, f"Source files: {file_count}, total {human_bytes(total_bytes)}")

    display = ProgressDisplay(total_bytes, verbosity, use_vt=use_vt)

    # Graceful interrupt: handler only records intent; the loop acts on it so
    # the in-flight copy always finishes (no half-written files).
    interrupt = {"first": None, "stop": False}

    def handle_sigint(signum, frame):
        now = time.time()
        if interrupt["first"] is not None and now - interrupt["first"] <= DOUBLE_PRESS_SECONDS:
            interrupt["stop"] = True
            display.log("  ^C again -- stopping after the current file finishes...")
        else:
            interrupt["first"] = now
            display.log(
                f"  ^C received -- this backup is only partial. Press Ctrl+C "
                f"again within {DOUBLE_PRESS_SECONDS}s to stop (current file "
                f"finishes; partial backup stays at {destination} and can be "
                f"resumed). Otherwise copying continues."
            )

    copied_bytes = 0
    copied_count = 0
    skipped_count = 0
    errors = []
    interrupted = False

    previous_handler = signal.getsignal(signal.SIGINT)
    signal.signal(signal.SIGINT, handle_sigint)
    try:
        for index, (src, rel) in enumerate(files, start=1):
            if interrupt["stop"]:
                interrupted = True
                break

            dst = destination / rel

            # Resume: skip files already copied. copy2 preserves mtime, so a
            # whole copy matches on both size and mtime; a file left corrupt or
            # truncated by a crash will differ and gets re-copied. (2s slack for
            # FAT's coarse timestamp resolution.)
            if resuming and dst.exists():
                try:
                    s_src, s_dst = src.stat(), dst.stat()
                    if (s_dst.st_size == s_src.st_size
                            and abs(s_dst.st_mtime - s_src.st_mtime) <= 2):
                        copied_bytes += s_dst.st_size
                        skipped_count += 1
                        log_line(log, f"SKIP  {rel} (already present)")
                        if verbosity >= 2:
                            display.log(f"  SKIP  [{index}/{file_count}] {rel}")
                        display.update(copied_bytes, name=str(rel))
                        continue
                except OSError:
                    pass  # fall through and re-copy

            try:
                dst.parent.mkdir(parents=True, exist_ok=True)
                if verbosity >= 2:
                    size = src.stat().st_size if src.exists() else 0
                    display.log(f"  COPY  [{index}/{file_count}] {rel} "
                                f"({human_bytes(size)})")
                elif verbosity >= 1:
                    display.log(f"  {rel}")
                shutil.copy2(src, dst)
                copied_count += 1
                try:
                    copied_bytes += src.stat().st_size
                except OSError:
                    pass
                log_line(log, f"OK    {rel}")
            except (OSError, shutil.Error) as exc:
                errors.append((rel, str(exc)))
                log_line(log, f"FAIL  {rel} -- {exc}")
                if verbosity >= 1:
                    display.log(f"  ! Failed: {rel} -- {exc}")

            display.update(copied_bytes, name=str(rel))
    finally:
        signal.signal(signal.SIGINT, previous_handler)

    display.close(completed=not interrupted and not errors)

    elapsed = time.time() - display.start
    processed = copied_count + skipped_count
    print(f"\n{'Stopped' if interrupted else 'Done'} in {elapsed:.1f}s.")
    summary = f"  Copied:  {copied_count} files"
    if skipped_count:
        summary += f", skipped {skipped_count} already present"
    summary += f" ({human_bytes(copied_bytes)})"
    print(summary)
    log_line(log, f"{'INTERRUPTED' if interrupted else 'Finished'} in "
                  f"{elapsed:.1f}s: {copied_count} copied, {skipped_count} skipped, "
                  f"{len(errors)} failed, {processed}/{file_count} of source "
                  f"({human_bytes(copied_bytes)})")

    if errors:
        print(f"  Failed:  {len(errors)} files")
        if verbosity >= 1:
            for rel, msg in errors[:20]:
                print(f"    - {rel}: {msg}")
            if len(errors) > 20:
                print(f"    ... and {len(errors) - 20} more")
        if log_path:
            print(f"  Full details written to {log_path}")

    # Marker lifecycle: keep it (and the folder) if we stopped early or some
    # files failed, so the next run can resume; otherwise the backup is whole.
    if interrupted:
        print(f"\n  Partial backup kept at {destination}")
        print(f"  Resume with:  python {Path(sys.argv[0]).name} "
              f"-s \"{source}\" --resume")
        if log:
            log.close()
        return 130

    if errors:
        if log:
            log.close()
        return 2

    clear_marker(destination)

    # Optional archiving: only a whole, successful backup is zipped.
    if make_zip:
        log_line(log, f"Creating archive of {destination}")
        if log:
            log.close()  # close so the log file is flushed into the archive
            log = None
        archive, ok = zip_backup(destination, verbosity, use_vt, zip_compress)
        if ok and not zip_keep:
            try:
                shutil.rmtree(destination)
                print(f"  Removed uncompressed folder; backup is now {archive}")
            except OSError as exc:
                print(f"  ! Kept folder -- could not remove {destination}: {exc}")
        elif not ok:
            print(f"  ! Archive not usable; kept uncompressed backup at {destination}")
        return 0

    if log:
        log.close()
    return 0


# --------------------------------------------------------------------------- #
# CLI
# --------------------------------------------------------------------------- #
def parse_args(argv):
    parser = argparse.ArgumentParser(
        description="Back up a drive or any file/folder path to a timestamped "
        f"folder under {DESTINATION_BASE}."
    )
    parser.add_argument(
        "-s", "--source", "-d", "--drive",
        dest="source",
        help="What to back up: a bare drive letter (e.g. D = the whole D:\\ "
        "drive) or any file/folder path. Prompts if omitted. (-d/--drive are "
        "kept as aliases.)",
    )
    parser.add_argument(
        "-v", "--verbosity",
        type=int,
        choices=(0, 1, 2),
        default=1,
        help="0 = bar with current filename only; 1 = bar + list of copied "
        "files (default); 2 = bar + detailed list (sizes, skips).",
    )
    parser.add_argument(
        "-y", "--yes",
        action="store_true",
        help="Skip the confirmation prompt.",
    )
    parser.add_argument(
        "--log",
        metavar="PATH",
        help="Write the log to PATH. Defaults to backup.log inside the "
        "backup folder.",
    )
    parser.add_argument(
        "--no-log",
        action="store_true",
        help="Disable logging (logging is on by default).",
    )
    parser.add_argument(
        "--resume",
        nargs="?",
        const="AUTO",
        metavar="PATH",
        help="Resume an interrupted backup. Bare --resume auto-resumes the "
        "latest incomplete backup for the drive; give a PATH to resume that "
        "folder. By default, the script offers to resume if one is found.",
    )
    parser.add_argument(
        "--no-resume",
        action="store_true",
        help="Always start a fresh backup, ignoring any incomplete one.",
    )
    parser.add_argument(
        "--zip",
        action="store_true",
        help="After a successful backup, compress it into a verified .zip and "
        "remove the uncompressed folder.",
    )
    parser.add_argument(
        "--zip-keep",
        action="store_true",
        help="With --zip, keep the uncompressed folder alongside the .zip "
        "instead of removing it.",
    )
    parser.add_argument(
        "--no-compress",
        action="store_true",
        help="With --zip, store files without compression (faster; best when "
        "the data is already compressed, e.g. video/photos).",
    )
    return parser.parse_args(argv)


def main(argv=None):
    args = parse_args(argv if argv is not None else sys.argv[1:])

    if args.no_log:
        log_path = None
    elif args.log:
        log_path = Path(args.log)
    else:
        log_path = "DEFAULT"  # resolved to <destination>/backup.log at run time

    if args.no_resume:
        resume_choice = "NONE"
    elif args.resume == "AUTO":
        resume_choice = "AUTO"
    elif args.resume:
        resume_choice = Path(args.resume)
    else:
        resume_choice = "PROMPT"

    use_vt = enable_vt_mode()

    try:
        source = prompt_for_source(args.source)
        return run_backup(source, args.verbosity, args.yes, log_path,
                          resume_choice, use_vt=use_vt, make_zip=args.zip,
                          zip_keep=args.zip_keep, zip_compress=not args.no_compress)
    except KeyboardInterrupt:
        # Only reachable outside the copy loop (e.g. during scan/prompt), where
        # nothing has been copied yet.
        print("\nInterrupted before copying began.")
        return 130
    except EOFError:
        # Closed/empty stdin (e.g. piped or redirected) hit an interactive
        # prompt -- exit cleanly instead of dumping a traceback.
        print("\nNo input available (stdin closed). "
              "Use -d/--drive, -y, and --resume/--no-resume for unattended runs.")
        return 1


if __name__ == "__main__":
    sys.exit(main())
