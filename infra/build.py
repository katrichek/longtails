import os
import subprocess
import sys
import time
from pathlib import Path


def acquire(handle):
    handle.seek(0)
    if os.name == "nt":
        import msvcrt

        while True:
            try:
                msvcrt.locking(handle.fileno(), msvcrt.LK_NBLCK, 1)
                return
            except OSError:
                time.sleep(1)
    else:
        import fcntl

        fcntl.flock(handle, fcntl.LOCK_EX)


def release(handle):
    handle.seek(0)
    if os.name == "nt":
        import msvcrt

        msvcrt.locking(handle.fileno(), msvcrt.LK_UNLCK, 1)
    else:
        import fcntl

        fcntl.flock(handle, fcntl.LOCK_UN)


def main():
    root = Path(__file__).resolve().parents[1]
    args = sys.argv[1:]
    lock_path = subprocess.check_output(
        ["git", "rev-parse", "--git-path", "longtails-build.lock"],
        cwd=root,
        text=True,
    ).strip()
    with (root / lock_path).open("a") as lock:
        print(f"Waiting for build lock in {root}...", flush=True)
        acquire(lock)
        try:
            print(f"Building {root}", flush=True)

            def run(command, check=True):
                return subprocess.run(command, cwd=root, check=check)

            # Never fetch build caches from the network: build everything locally.
            if run(
                ["lake", "exe", "mk_all", "--lib", "LongTails"], check=False
            ).returncode:
                run(["lake", "exe", "mk_all", "--lib", "LongTails", "--check"])
            run(["lake", "build", "--no-cache", *args])
        finally:
            release(lock)


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as error:
        sys.exit(error.returncode)
