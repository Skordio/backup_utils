#!/usr/bin/env python3
"""Back up a removable drive to a timestamped folder.

Python port of backup.ps1, with selectable drive letter, adjustable
verbosity, a progress bar pinned to the bottom of the terminal, graceful
double-Ctrl+C handling, default logging, and resume of interrupted backups.

Standard library only -- no third-party packages required.
"""

import argparse
import concurrent.futures
import ctypes
import json
import os
import shutil
import signal
import string
import subprocess
import sys
import time
import zipfile
import zlib
from datetime import datetime
from pathlib import Path

DESTINATION_BASE = Path(r"C:\Users\skord\Backups\Flipper")
MARKER_NAME = ".backup_incomplete.json"
LOG_NAME = "backup.log"
DOUBLE_PRESS_SECONDS = 5
COPY_CHUNK = 1024 * 1024  # read/write granularity for the progress-aware copy
PROGRESS_INTERVAL = 0.2   # min seconds between bar redraws during a single file
ZIP_MT_BUDGET = 256 * 1024 * 1024  # max in-flight uncompressed bytes (bounds RAM)
ZIP_MT_LARGE = 64 * 1024 * 1024    # files above this stream single-threaded
SPEED_WINDOW = 3.0        # seconds of history used for the live transfer-speed figure
ETA_WINDOW = 20.0         # seconds of history the ETA regression looks at
ETA_SMOOTH = 0.25         # EWMA weight applied to the ETA output
SAMPLE_INTERVAL = 0.1     # min seconds between recorded history samples (bounds memory)
MIN_ETA_SPAN = 1.0        # need this much window time before showing an ETA number
ETA_MIN_BW = 1_000_000    # bytes/sec; a per-byte rate slower than this is overhead, not streaming
ETA_BYTE_FLOOR = 96_000_000  # window must move this many bytes before the byte term is trusted
ETA_CAP_MULT = 2.0        # per-file-branch ETA can't exceed this x the cumulative-file-rate projection


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
    # No drive-letter concept off Windows; callers fall back to path input.
    return []


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
    """Walk the source, returning (files, total_bytes, empty_dirs).

    files is a list of (src_path, relative_path) tuples. empty_dirs is a list of
    relative paths for directories that contain no files or subdirs, so the copy
    step can recreate them (the per-file copy only makes parents of files). A
    single-file source yields one entry whose relative path is just the file
    name and no empty dirs.
    """
    files = []
    empty_dirs = []
    total = 0
    if source.is_file():
        try:
            total = source.stat().st_size
        except OSError:
            total = 0
        return [(source, Path(source.name))], total, empty_dirs
    for root, dirs, names in os.walk(source):
        for name in names:
            src = Path(root) / name
            try:
                size = src.stat().st_size
            except OSError:
                size = 0
            files.append((src, src.relative_to(source)))
            total += size
        # A leaf directory with nothing in it would otherwise vanish from the
        # backup; record it so it can be recreated. (Parents are remade via
        # mkdir(parents=True) when their own leaf entries are created.)
        if not names and not dirs:
            rel = Path(root).relative_to(source)
            if str(rel) != ".":
                empty_dirs.append(rel)
    return files, total, empty_dirs


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

    def __init__(self, total_bytes, verbosity, stream=None, use_vt=True,
                 total_files=0, eta_log_path=None):
        self.total = total_bytes
        self.total_files = total_files
        self.verbosity = verbosity
        self.stream = stream if stream is not None else sys.stderr
        self.is_tty = bool(getattr(self.stream, "isatty", lambda: False)())
        self.use_vt = use_vt
        self.max_bar = 34
        self.done = 0
        self.last_name = ""
        self.start = time.time()
        self._next_milestone = 10  # for non-TTY percentage reporting
        self._samples = []         # (timestamp, bytes_done, files_done) history
        self._last_render = 0.0    # last TTY redraw time, for update() throttling
        self._last_sample_t = 0.0  # last recorded-sample time, for decimation
        self._files_done = 0
        self._kb = 0.0             # latest raw sec/byte coefficient (for debug log)
        self._kf = 0.0             # latest raw sec/file coefficient (for debug log)
        self._eta_ewma = None      # smoothed ETA seconds
        self._eta_seconds = None   # latest ETA estimate (cached for render/log)
        self._eta_log = open(eta_log_path, "w", encoding="utf-8") if eta_log_path else None
        if self._eta_log:
            self._eta_log.write("elapsed,bytes_done,total_bytes,files_done,"
                                "total_files,speed_bps,kb,kf,eta_seconds\n")

    # -- internals ---------------------------------------------------------- #
    def _term_width(self):
        return shutil.get_terminal_size((80, 24)).columns

    def _clear_seq(self):
        if self.use_vt:
            return "\r\033[2K"
        return "\r" + " " * (self._term_width() - 1) + "\r"

    def _record_sample(self, now, done, files):
        """Remember (now, done, files); decimate to SAMPLE_INTERVAL and trim to
        ETA_WINDOW. Returns True if a *new* sample was appended (vs. refreshing
        the latest), so callers can recompute the ETA only when data changed."""
        if self._samples and now - self._last_sample_t < SAMPLE_INTERVAL:
            self._samples[-1] = (now, done, files)  # keep newest reading fresh
            return False
        self._samples.append((now, done, files))
        self._last_sample_t = now
        cutoff = now - ETA_WINDOW
        while len(self._samples) > 2 and self._samples[0][0] < cutoff:
            self._samples.pop(0)
        return True

    def _current_speed(self):
        """Bytes/sec over the recent SPEED_WINDOW tail of the shared history;
        falls back to the cumulative average until enough history exists."""
        cutoff = self._samples[-1][0] - SPEED_WINDOW if self._samples else 0
        tail = [s for s in self._samples if s[0] >= cutoff]
        if len(tail) >= 2:
            t0, d0, _ = tail[0]
            t1, d1, _ = tail[-1]
            span = t1 - t0
            if span > 0:
                return max(0.0, (d1 - d0) / span)
        elapsed = time.time() - self.start
        return (self.done / elapsed) if elapsed > 0 else 0.0

    def _estimate_eta(self):
        """Seconds remaining, modelling elapsed time as k_b*bytes + k_f*files via
        least squares over the recent window (predictors normalised so the fit is
        well-conditioned across the huge bytes-vs-files scale gap).

        The per-file term is the robust backbone for tiny-file trees. The per-byte
        term is only trusted during genuine streaming -- the window must have moved
        ETA_BYTE_FLOOR bytes at a believable bandwidth -- otherwise overhead would
        be misattributed to a giant per-byte cost and, times the remaining bytes,
        blow the estimate up to hours. The per-file/fallback branch is capped at a
        multiple of the cumulative file-rate projection; a real streaming estimate
        is never capped (it would wreck big-file backups). Output is EWMA-smoothed
        and returned; None until there is enough history. (Tuned against a real
        ~30k-file Flipper backup; see git history.)"""
        s = self._samples
        if len(s) < 2 or s[-1][0] - s[0][0] < MIN_ETA_SPAN:
            return None
        t0, b0, f0 = s[0]
        bs = self.total if self.total > 0 else 1.0
        fs = self.total_files if self.total_files > 0 else 1.0

        Sbb = Sff = Sbf = Sbt = Sft = 0.0
        for (t, b, f) in s:
            db, df, dt = (b - b0) / bs, (f - f0) / fs, t - t0
            Sbb += db * db
            Sff += df * df
            Sbf += db * df
            Sbt += db * dt
            Sft += df * dt
        det = Sbb * Sff - Sbf * Sbf

        kb = kf = None                             # solve in normalised space
        if det > 1e-9 * (Sbb * Sff + 1):
            kb = (Sbt * Sff - Sft * Sbf) / det / bs
            kf = (Sft * Sbb - Sbt * Sbf) / det / fs
        kf_only = (Sft / Sff / fs) if Sff > 0 else None

        rem_b = max(0, self.total - self.done)
        rem_f = max(0, self.total_files - self._files_done)
        win_bytes = s[-1][1] - s[0][1]
        trust_bytes = (kb is not None and kb > 0 and win_bytes >= ETA_BYTE_FLOOR
                       and kb <= 1.0 / ETA_MIN_BW)

        capped = True
        if trust_bytes and kf is not None and kf >= 0:
            self._kb, self._kf = kb, kf
            eta = kb * rem_b + kf * rem_f
            capped = False                         # never clip a real streaming estimate
        elif kf_only is not None:
            self._kb, self._kf = 0.0, kf_only
            eta = kf_only * rem_f
        elif Sbb > 0:                              # files flat, only bytes moving
            self._kb, self._kf = Sbt / Sbb / bs, 0.0
            eta = self._kb * rem_b
        else:
            return None

        if capped and self._files_done > 0:
            elapsed = s[-1][0] - self.start      # latest sample time == "now"
            if elapsed > 0:
                eta = min(eta, ETA_CAP_MULT * rem_f / (self._files_done / elapsed))
        eta = max(0.0, eta)

        self._eta_ewma = eta if self._eta_ewma is None \
            else ETA_SMOOTH * eta + (1 - ETA_SMOOTH) * self._eta_ewma
        return self._eta_ewma

    @staticmethod
    def _format_eta(eta):
        """Fixed-width 'ETA ...' string; h/m/s so it never overflows on long runs."""
        if eta is None:
            return "ETA  --"
        s = int(eta)
        if s < 60:
            return f"ETA {s:3d}s"
        if s < 3600:
            return f"ETA {s // 60}m{s % 60:02d}s"
        return f"ETA {s // 3600}h{(s % 3600) // 60:02d}m"

    def _render_bar(self):
        term = self._term_width()
        frac = (self.done / self.total) if self.total else 1.0
        frac = min(frac, 1.0)
        speed = f"{human_bytes(self._current_speed())}/s"
        suffix = (
            f" {frac * 100:5.1f}%  "
            f"{human_bytes(self.done)}/{human_bytes(self.total)}  "
            f"{speed:>10}  "
            f"{self._format_eta(self._eta_seconds):>8}"
        )
        # Size the bar to the terminal: 2 cols for the brackets plus 1 the
        # term-1 clamp below reserves, so a full-width line never gets its last
        # character (e.g. the ETA unit) shaved off.
        bar_width = max(10, min(self.max_bar, term - len(suffix) - 3))
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
    def update(self, done, name=None, min_interval=0.0, files=None):
        now = time.time()
        self.done = done
        if name is not None:
            self.last_name = name
        if files is not None:
            self._files_done = files
        if self._record_sample(now, done, self._files_done):
            self._eta_seconds = self._estimate_eta()  # recompute only on new data
            self._log_eta(now)
        if self.is_tty:
            # Throttle terminal writes during a single large file; state above
            # is already current, so a skipped frame loses nothing.
            if min_interval and (now - self._last_render) < min_interval:
                return
            self._last_render = now
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

    def _log_eta(self, now):
        """Append a CSV row of raw inputs + estimate when --debug-eta is active."""
        if not self._eta_log:
            return
        eta = "" if self._eta_seconds is None else f"{self._eta_seconds:.1f}"
        self._eta_log.write(
            f"{now - self.start:.2f},{self.done},{self.total},{self._files_done},"
            f"{self.total_files},{self._current_speed():.0f},"
            f"{self._kb or 0:.3e},{self._kf or 0:.3e},{eta}\n")
        self._eta_log.flush()

    def close(self, completed=True):
        """Draw the final bar. Only a completed run is forced to 100%; an
        interrupted or partially-failed run keeps its true position."""
        if self._eta_log:
            self._eta_log.close()
            self._eta_log = None
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


def find_incomplete(source, dest_base):
    """Return the most recent incomplete backup folder for a source, or None."""
    if not dest_base.exists():
        return None
    key = str(source)
    candidates = []
    for child in dest_base.iterdir():
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
def find_7zip():
    """Return a path to a 7-Zip executable, or None. Checks PATH first, then the
    standard Windows install locations (7-Zip is commonly installed but not on
    PATH). 7-Zip compresses zip entries across all cores, several times faster
    than the single-threaded stdlib writer."""
    for name in ("7z", "7za"):
        found = shutil.which(name)
        if found:
            return found
    if os.name == "nt":
        for base in (os.environ.get("ProgramFiles", r"C:\Program Files"),
                     os.environ.get("ProgramFiles(x86)", r"C:\Program Files (x86)")):
            cand = Path(base) / "7-Zip" / "7z.exe"
            if cand.is_file():
                return str(cand)
    return None


def _zip_with_7zip(sevenzip, destination, archive, compress, threads=None):
    """Build ``archive`` from the contents of ``destination`` using 7-Zip
    (multithreaded). Returns True on success. Output stays a standard .zip --
    the caller verifies it with the stdlib reader just like the stdlib writer."""
    if archive.exists():
        try:
            archive.unlink()  # 7z would *update* an existing archive, not replace
        except OSError as exc:
            print(f"  ! Could not replace existing archive: {exc}")
            return False
    print(f"  Using 7-Zip (multithreaded): {sevenzip}")
    level = "-mx=6" if compress else "-mx=0"
    mmt = f"-mmt={threads}" if threads else "-mmt=on"
    # cwd=destination + '*' stores paths relative to the backup root (incl. empty
    # dirs and dot-prefixed files). -bso0 hides the file list; -bsp1 shows the
    # live percentage; errors still arrive on stderr.
    cmd = [sevenzip, "a", "-tzip", level, mmt, "-bso0", "-bsp1",
           "--", str(archive), "*"]
    try:
        result = subprocess.run(cmd, cwd=str(destination), stderr=subprocess.PIPE,
                                text=True)
    except OSError as exc:
        print(f"  ! Could not run 7-Zip: {exc}")
        return False
    if result.returncode != 0:
        print(f"  ! 7-Zip failed (exit {result.returncode}). "
              f"{(result.stderr or '').strip()[:300]}")
        return False
    return True


def _zip_with_stdlib(destination, archive, entries, empty_dirs, total,
                     verbosity, use_vt, compress):
    """Single-threaded stdlib writer. Returns (ok, manifest) where manifest maps
    each archived file name to its uncompressed size (successfully written files
    only)."""
    method = zipfile.ZIP_DEFLATED if compress else zipfile.ZIP_STORED
    display = ProgressDisplay(total, verbosity, use_vt=use_vt,
                              total_files=len(entries))
    done = 0
    written = 0
    manifest = {}
    try:
        with zipfile.ZipFile(archive, "w", method, allowZip64=True) as zf:
            for p in entries:
                rel = p.relative_to(destination)
                try:
                    size = p.stat().st_size
                    zf.write(p, str(rel))
                    written += 1
                    done += size
                    manifest[str(rel).replace(os.sep, "/")] = size
                    if verbosity >= 2:
                        display.log(f"  ZIP   {rel}")
                except OSError as exc:
                    display.log(f"  ! zip failed: {rel} -- {exc}")
                display.update(done, name=str(rel), files=written)
            for d in empty_dirs:
                rel = d.relative_to(destination)
                try:
                    zf.write(d, str(rel))
                except OSError as exc:
                    display.log(f"  ! zip failed (dir): {rel} -- {exc}")
        display.close(completed=True)
    except OSError as exc:
        display.close(completed=False)
        print(f"  ! Could not create archive: {exc}")
        return False, manifest
    return True, manifest


def _compress_entry(path, arcname, compress):
    """Thread-pool worker: read + CRC + deflate one file. Returns a tuple ready
    for _write_zip_entry. zlib's crc32/deflate and the file read all release the
    GIL, so a pool of these genuinely parallelises across cores. Falls back to
    STORED when deflate doesn't shrink the file (or compression is off)."""
    st = path.stat()
    data = path.read_bytes()
    crc = zlib.crc32(data) & 0xFFFFFFFF
    dt = time.localtime(st.st_mtime)[:6]
    if dt[0] < 1980:
        dt = (1980, 1, 1, 0, 0, 0)  # zip epoch floor
    ext_attr = (st.st_mode & 0xFFFF) << 16
    if compress:
        co = zlib.compressobj(6, zlib.DEFLATED, -15)  # raw DEFLATE stream
        payload = co.compress(data) + co.flush()
        if len(payload) < len(data):
            return (arcname, dt, ext_attr, crc, len(data), payload, zipfile.ZIP_DEFLATED)
    return (arcname, dt, ext_attr, crc, len(data), data, zipfile.ZIP_STORED)


def _write_zip_entry(zf, result):
    """Main-thread: inject a pre-compressed entry (from _compress_entry) into the
    open ZipFile. Uses the public ZipInfo.FileHeader() for the local header and
    lets ZipFile.close() build the central directory (incl. zip64). Only the main
    thread touches zf.fp, so writes stay ordered. Returns the uncompressed size."""
    arcname, dt, ext_attr, crc, file_size, payload, ctype = result
    zi = zipfile.ZipInfo(arcname, dt)
    zi.compress_type = ctype
    zi.external_attr = ext_attr
    zi.CRC = crc
    zi.file_size = file_size
    zi.compress_size = len(payload)
    zi.header_offset = zf.fp.tell()
    zf.fp.write(zi.FileHeader())
    zf.fp.write(payload)
    zf.start_dir = zf.fp.tell()
    zf.filelist.append(zi)
    zf.NameToInfo[zi.filename] = zi
    zf._didModify = True
    return file_size


def _write_empty_dir_entry(zf, arcname):
    """Write a zero-length directory entry the same way as _write_zip_entry."""
    zi = zipfile.ZipInfo(arcname)
    zi.compress_type = zipfile.ZIP_STORED
    zi.external_attr = (0o40755 << 16) | 0x10  # dir mode + FILE_ATTRIBUTE_DIRECTORY
    zi.CRC = 0
    zi.file_size = 0
    zi.compress_size = 0
    zi.header_offset = zf.fp.tell()
    zf.fp.write(zi.FileHeader())
    zf.start_dir = zf.fp.tell()
    zf.filelist.append(zi)
    zf.NameToInfo[zi.filename] = zi
    zf._didModify = True


def _zip_with_threads(destination, archive, entries, empty_dirs, total,
                      verbosity, use_vt, compress, workers):
    """Multithreaded stdlib writer: compress files across a thread pool, write
    entries from the main thread. Returns (ok, manifest). RAM is bounded by a
    byte budget; files above ZIP_MT_LARGE stream single-threaded (a single file
    can't be split into one parallel DEFLATE member anyway)."""
    print(f"  Using built-in multithreaded zip ({workers} threads)")
    display = ProgressDisplay(total, verbosity, use_vt=use_vt,
                              total_files=len(entries))
    method = zipfile.ZIP_DEFLATED if compress else zipfile.ZIP_STORED
    manifest = {}
    done = 0
    written = 0
    pending = iter(entries)
    exhausted = False
    inflight = {}          # future -> input size
    inflight_bytes = 0
    try:
        with zipfile.ZipFile(archive, "w", allowZip64=True) as zf, \
                concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
            while not exhausted or inflight:
                # Fill the pool up to the byte budget / queue depth.
                while (not exhausted and inflight_bytes < ZIP_MT_BUDGET
                       and len(inflight) < workers * 3):
                    p = next(pending, None)
                    if p is None:
                        exhausted = True
                        break
                    rel = str(p.relative_to(destination)).replace(os.sep, "/")
                    try:
                        size = p.stat().st_size
                    except OSError as exc:
                        display.log(f"  ! zip failed: {rel} -- {exc}")
                        continue
                    if size > ZIP_MT_LARGE:
                        try:
                            zf.write(p, rel, compress_type=method)
                            manifest[rel] = size
                            written += 1
                            done += size
                            if verbosity >= 2:
                                display.log(f"  ZIP   {rel}")
                            display.update(done, name=rel, files=written)
                        except OSError as exc:
                            display.log(f"  ! zip failed: {rel} -- {exc}")
                        continue
                    fut = pool.submit(_compress_entry, p, rel, compress)
                    inflight[fut] = size
                    inflight_bytes += size
                # Drain whatever has finished (at least one).
                if inflight:
                    finished, _ = concurrent.futures.wait(
                        inflight, return_when=concurrent.futures.FIRST_COMPLETED)
                    for fut in finished:
                        inflight_bytes -= inflight.pop(fut)
                        try:
                            result = fut.result()
                        except OSError as exc:
                            display.log(f"  ! zip failed -- {exc}")
                            continue
                        done += _write_zip_entry(zf, result)
                        written += 1
                        manifest[result[0]] = result[4]
                        if verbosity >= 2:
                            display.log(f"  ZIP   {result[0]}")
                        display.update(done, name=result[0], files=written)
            for d in empty_dirs:
                rel = str(d.relative_to(destination)).replace(os.sep, "/").rstrip("/") + "/"
                _write_empty_dir_entry(zf, rel)
            display.close(completed=True)
    except OSError as exc:
        display.close(completed=False)
        print(f"  ! Could not create archive: {exc}")
        return False, manifest
    return True, manifest


def zip_backup(destination, verbosity, use_vt, compress=True, engine="auto",
               threads=None):
    """Compress everything in ``destination`` into a sibling .zip.

    Uses 7-Zip (multithreaded) when available, else the stdlib writer; either
    way the result is a standard .zip verified with the stdlib reader before the
    caller is allowed to delete the source folder. Returns (archive_path, ok).
    """
    archive = destination.with_name(destination.name + ".zip")

    entries = []
    empty_dirs = []
    total = 0
    for root, dirs, names in os.walk(destination):
        for name in names:
            p = Path(root) / name
            try:
                total += p.stat().st_size
            except OSError:
                pass
            entries.append(p)
        # Preserve leaf directories that hold no files or subdirs; writing the
        # per-dir entry recreates any intermediate parents on extraction too.
        if not names and not dirs and Path(root) != destination:
            empty_dirs.append(Path(root))
    expected_dirs = {str(d.relative_to(destination)).replace(os.sep, "/").rstrip("/") + "/"
                     for d in empty_dirs}

    print(f"\nCompressing {len(entries)} files into {archive.name} ...")
    sevenzip = find_7zip() if engine in ("auto", "7zip") else None
    if engine == "7zip" and not sevenzip:
        print("  ! 7-Zip not found; using the built-in writer instead.")

    if sevenzip and engine != "builtin":
        # 7-Zip archives every entry or fails wholesale, so the expected manifest
        # is the full file set (sizes from the scan).
        manifest = {}
        for p in entries:
            try:
                manifest[str(p.relative_to(destination)).replace(os.sep, "/")] = p.stat().st_size
            except OSError:
                pass
        ok = _zip_with_7zip(sevenzip, destination, archive, compress, threads)
    else:
        workers = threads if threads else max(1, (os.cpu_count() or 2) - 1)
        if compress and workers > 1:
            try:
                ok, manifest = _zip_with_threads(destination, archive, entries,
                                                 empty_dirs, total, verbosity,
                                                 use_vt, compress, workers)
            except Exception as exc:  # incl. any zipfile-internals drift
                print(f"  ! Multithreaded zip failed ({exc}); "
                      f"falling back to single-threaded.")
                try:
                    archive.unlink()
                except OSError:
                    pass
                ok, manifest = _zip_with_stdlib(destination, archive, entries,
                                                empty_dirs, total, verbosity,
                                                use_vt, compress)
        else:
            ok, manifest = _zip_with_stdlib(destination, archive, entries,
                                            empty_dirs, total, verbosity, use_vt,
                                            compress)
    if not ok:
        return archive, False

    # Verify before the caller is allowed to delete the source folder: CRC-check
    # every entry, then confirm each expected file/dir is present and that files
    # are the right size (catches truncated or dropped entries, not just bit rot).
    try:
        with zipfile.ZipFile(archive) as zf:
            bad = zf.testzip()
            names = set(zf.namelist())
            missing = [a for a, sz in manifest.items()
                       if a not in names or zf.getinfo(a).file_size != sz]
            missing += [d for d in expected_dirs if d not in names]
    except (OSError, zipfile.BadZipFile) as exc:
        print(f"  ! Archive verification failed: {exc}")
        return archive, False
    if bad is not None or missing:
        print(f"  ! Archive verification failed "
              f"(corrupt entry={bad}, {len(missing)} entries missing or wrong size).")
        return archive, False

    print(f"  Archived and verified: {archive} "
          f"({human_bytes(archive.stat().st_size)}, {len(manifest)} files)")
    return archive, True


# --------------------------------------------------------------------------- #
# Backup
# --------------------------------------------------------------------------- #
def copy_with_progress(src, dst, on_chunk):
    """Copy ``src`` to ``dst`` like ``shutil.copy2`` (data + metadata), invoking
    ``on_chunk(file_bytes_so_far)`` after each chunk so a large file keeps the
    progress bar moving instead of blocking on one monolithic copy. Returns the
    number of bytes copied.

    ``copy2`` == ``copyfile`` + ``copystat``; replicating ``copystat`` preserves
    the mtime/mode that the resume-skip check relies on.
    """
    copied = 0
    with open(src, "rb") as fsrc, open(dst, "wb") as fdst:
        while True:
            chunk = fsrc.read(COPY_CHUNK)
            if not chunk:
                break
            fdst.write(chunk)
            copied += len(chunk)
            on_chunk(copied)
    shutil.copystat(src, dst)
    return copied


def run_backup(source, verbosity, assume_yes, log_path, resume_choice,
               use_vt=True, make_zip=False, zip_keep=False, zip_compress=True,
               dest_base=DESTINATION_BASE, eta_log_path=None,
               zip_engine="auto", zip_threads=None):
    label = describe_source(source)

    # ------------------------------------------------------------------ #
    # Decide destination: fresh timestamped folder, or resume an existing one.
    # ------------------------------------------------------------------ #
    destination = None
    resuming = False
    if resume_choice == "NONE":
        pass  # forced fresh
    elif isinstance(resume_choice, Path):
        if not (resume_choice / MARKER_NAME).is_file():
            print(f"\nCannot resume: no interrupted backup found at {resume_choice}")
            print(f"  (expected a {MARKER_NAME} marker inside that folder).")
            return 1
        destination = resume_choice
        resuming = True
    else:  # "AUTO" (bare --resume) or "PROMPT" (default: ask if one is found)
        found = find_incomplete(source, dest_base)
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
        destination = dest_base / timestamp
        # Second-resolution timestamps collide for back-to-back runs; bump a
        # suffix until both the folder and its .zip sibling are free so a fresh
        # backup never merges into (or overwrites) an earlier one.
        suffix = 1
        while (destination.exists()
               or destination.with_name(destination.name + ".zip").exists()):
            destination = dest_base / f"{timestamp}_{suffix}"
            suffix += 1

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
    files, total_bytes, empty_dirs = gather_files(source)
    file_count = len(files)
    if file_count == 0 and not empty_dirs:
        print("Nothing to copy -- the source is empty or unreadable.")
        return 0
    print(f"Found {file_count} files, {human_bytes(total_bytes)} total.\n")

    destination.mkdir(parents=True, exist_ok=True)
    # Recreate empty source directories up front so the backup mirrors the tree
    # (the copy loop below only makes parents of the files it writes).
    for rel in empty_dirs:
        try:
            (destination / rel).mkdir(parents=True, exist_ok=True)
        except OSError:
            pass
    started = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    write_marker(destination, source, label, started, file_count, total_bytes)

    log = open_log(log_path, append=resuming)
    log_line(log, f"{'Resumed' if resuming else 'Backup started'}: "
                  f"{label} -> {destination}")
    log_line(log, f"Source files: {file_count}, total {human_bytes(total_bytes)}")

    display = ProgressDisplay(total_bytes, verbosity, use_vt=use_vt,
                              total_files=file_count, eta_log_path=eta_log_path)

    # Graceful interrupt: handler only records intent; the loop acts on it so
    # the in-flight copy always finishes (no half-written files).
    interrupt = {"first": None, "stop": False}

    def handle_sigint(signum, frame):
        now = time.time()
        if interrupt["first"] is not None and now - interrupt["first"] <= DOUBLE_PRESS_SECONDS:
            interrupt["stop"] = True
            display.log("  ^C again -- will stop once the current file finishes. "
                        "A large file may take a moment; the %/speed keep updating "
                        "until then.")
        else:
            interrupt["first"] = now
            display.log(
                f"  ^C received -- this backup is only partial. Press Ctrl+C "
                f"again within {DOUBLE_PRESS_SECONDS}s to stop (current file "
                f"finishes; partial backup stays at {destination} and can be "
                f"resumed). Otherwise copying continues."
            )

    copied_bytes = 0
    skipped_bytes = 0
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
                        skipped_bytes += s_dst.st_size
                        skipped_count += 1
                        log_line(log, f"SKIP  {rel} (already present)")
                        if verbosity >= 2:
                            display.log(f"  SKIP  [{index}/{file_count}] {rel}")
                        display.update(copied_bytes + skipped_bytes, name=str(rel),
                                       files=copied_count + skipped_count)
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
                base = copied_bytes + skipped_bytes  # progress before this file
                done_files = copied_count + skipped_count  # current file not done yet
                display.update(base, name=str(rel), min_interval=PROGRESS_INTERVAL,
                               files=done_files)
                n = copy_with_progress(
                    src, dst,
                    lambda file_done, base=base, rel=rel, df=done_files:
                        display.update(base + file_done, name=str(rel),
                                       min_interval=PROGRESS_INTERVAL, files=df),
                )
                copied_count += 1
                copied_bytes += n
                log_line(log, f"OK    {rel}")
            except (OSError, shutil.Error) as exc:
                errors.append((rel, str(exc)))
                log_line(log, f"FAIL  {rel} -- {exc}")
                if verbosity >= 1:
                    display.log(f"  ! Failed: {rel} -- {exc}")

            display.update(copied_bytes + skipped_bytes, name=str(rel),
                           files=copied_count + skipped_count)
    finally:
        signal.signal(signal.SIGINT, previous_handler)

    display.close(completed=not interrupted and not errors)

    elapsed = time.time() - display.start
    processed = copied_count + skipped_count
    print(f"\n{'Stopped' if interrupted else 'Done'} in {elapsed:.1f}s.")
    summary = f"  Copied:  {copied_count} files ({human_bytes(copied_bytes)})"
    if skipped_count:
        summary += (f", skipped {skipped_count} already present "
                    f"({human_bytes(skipped_bytes)})")
    print(summary)
    log_line(log, f"{'INTERRUPTED' if interrupted else 'Finished'} in "
                  f"{elapsed:.1f}s: {copied_count} copied ({human_bytes(copied_bytes)}), "
                  f"{skipped_count} skipped ({human_bytes(skipped_bytes)}), "
                  f"{len(errors)} failed, {processed}/{file_count} of source")

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
        try:
            archive, ok = zip_backup(destination, verbosity, use_vt, zip_compress,
                                     engine=zip_engine, threads=zip_threads)
        except KeyboardInterrupt:
            # The backup itself is complete and verified; only the optional
            # archive was interrupted. Drop the partial .zip and keep the folder.
            archive = destination.with_name(destination.name + ".zip")
            try:
                archive.unlink()
            except OSError:
                pass
            print(f"\n  Archiving interrupted; uncompressed backup kept at {destination}")
            return 0
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
        "-o", "--output",
        metavar="DIR",
        help="Base directory to write timestamped backup folders into. "
        f"Defaults to {DESTINATION_BASE}.",
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
    parser.add_argument(
        "--zip-engine",
        choices=("auto", "7zip", "builtin"),
        default="auto",
        help="Which zip backend to use: auto (7-Zip if installed, else the "
        "built-in multithreaded writer; default), 7zip (force 7-Zip), or "
        "builtin (force the built-in multithreaded writer).",
    )
    parser.add_argument(
        "--zip-threads",
        type=int,
        metavar="N",
        help="Worker threads for the built-in zip writer (also passed to 7-Zip). "
        "Defaults to one less than the CPU count.",
    )
    parser.add_argument(
        "--debug-eta",
        metavar="CSV",
        help="Diagnostic: log raw progress + ETA estimates to CSV each sample, "
        "for tuning the ETA model. Safe to ignore.",
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

    dest_base = Path(args.output).expanduser() if args.output else DESTINATION_BASE
    eta_log_path = Path(args.debug_eta).expanduser() if args.debug_eta else None

    use_vt = enable_vt_mode()

    try:
        source = prompt_for_source(args.source)
        return run_backup(source, args.verbosity, args.yes, log_path,
                          resume_choice, use_vt=use_vt, make_zip=args.zip,
                          zip_keep=args.zip_keep, zip_compress=not args.no_compress,
                          dest_base=dest_base, eta_log_path=eta_log_path,
                          zip_engine=args.zip_engine, zip_threads=args.zip_threads)
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
