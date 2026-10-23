"""Verify, or reproduce in a fresh directory, the optional offline Three.js bundle."""

from __future__ import annotations

import argparse
import base64
from hashlib import sha256, sha512
import io
import json
from pathlib import Path, PurePosixPath
import platform
import shutil
import subprocess
import sys
import tarfile
from urllib.request import urlopen


HERE = Path(__file__).resolve().parent


def digest(data: bytes) -> str:
    return sha256(data).hexdigest()


def verify(manifest: dict) -> None:
    for name, record in manifest["artifacts"].items():
        data = (HERE / name).read_bytes()
        if len(data) != record["bytes"] or digest(data) != record["sha256"]:
            raise ValueError("Vendored artifact changed: " + name)
    print("PASS: vendored bundle, entry source, and original Three.js license hashes")


def fetch(package: dict, archive_dir: Path | None) -> bytes:
    if archive_dir is not None:
        data = (archive_dir / package["archive_filename"]).read_bytes()
    else:
        with urlopen(package["url"], timeout=90) as response:
            data = response.read()
    integrity = "sha512-" + base64.b64encode(sha512(data).digest()).decode("ascii")
    if integrity != package["integrity"] or digest(data) != package["sha256"]:
        raise ValueError("Package archive hash mismatch: " + package["name"])
    return data


def extract(data: bytes, destination: Path) -> None:
    destination.mkdir(parents=True)
    with tarfile.open(fileobj=io.BytesIO(data), mode="r:gz") as archive:
        for member in archive.getmembers():
            parts = PurePosixPath(member.name).parts
            if not parts or parts[0] != "package" or ".." in parts or member.issym() or member.islnk():
                raise ValueError("Unsafe package archive member")
            target = destination.joinpath(*parts[1:])
            if not target.resolve().is_relative_to(destination.resolve()):
                raise ValueError("Package member escapes its destination")
            if member.isfile():
                target.parent.mkdir(parents=True, exist_ok=True)
                stream = archive.extractfile(member)
                if stream is None:
                    raise ValueError("Missing package member")
                target.write_bytes(stream.read())


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-only", action="store_true")
    parser.add_argument(
        "--work-dir", type=Path, help="fresh output directory; repository assets stay unchanged"
    )
    parser.add_argument(
        "--archive-dir", type=Path, help="use already downloaded pinned archives without network"
    )
    args = parser.parse_args()
    manifest = json.loads((HERE / "manifest.json").read_text(encoding="utf-8"))
    verify(manifest)
    if args.verify_only:
        return
    if args.work_dir is None:
        parser.error("provide --verify-only or a fresh --work-dir")
    work = args.work_dir.resolve()
    if work.exists() or work.is_relative_to(HERE):
        parser.error("--work-dir must be fresh and outside demo/vendor")
    if platform.machine().lower() not in {"amd64", "x86_64"}:
        parser.error("the pinned rebuild binaries support x86-64 Windows and Linux")
    system = "win32-x64" if sys.platform == "win32" else "linux-x64" if sys.platform == "linux" else None
    if system is None:
        parser.error("the pinned rebuild binaries support x86-64 Windows and Linux")
    work.mkdir(parents=True)
    three = manifest["source"]
    bundler = manifest["build_tools"][system]
    extract(fetch(three, args.archive_dir), work / "node_modules/three")
    extract(fetch(bundler, args.archive_dir), work / "esbuild")
    executable = work / "esbuild" / bundler["executable"]
    if digest(executable.read_bytes()) != bundler["executable_sha256"]:
        raise ValueError("Extracted esbuild executable hash mismatch")
    if sys.platform != "win32":
        executable.chmod(0o755)
    shutil.copyfile(HERE / "entry.js", work / "entry.js")
    version = subprocess.check_output([str(executable), "--version"], text=True).strip()
    if version != bundler["version"]:
        raise ValueError("Unexpected esbuild version")
    output = work / "three-orbit.min.js"
    subprocess.run(
        [str(executable), "entry.js", *manifest["build_options"], "--outfile=" + str(output)],
        cwd=work,
        check=True,
    )
    if digest(output.read_bytes()) != manifest["artifacts"]["three-orbit.min.js"]["sha256"]:
        raise ValueError("Rebuilt bundle differs from the distributed artifact")
    if (work / "node_modules/three/LICENSE").read_bytes() != (HERE / "LICENSE-three.txt").read_bytes():
        raise ValueError("The distributed license differs from the original package")
    print("PASS: fresh source rebuild exactly matches the distributed bundle")


if __name__ == "__main__":
    main()
