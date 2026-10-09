#!/usr/bin/env python3
"""Check release hashes and exact extracted source identity, not Lean validity.

Copyright 2026 Rohit Kumar Jha
SPDX-License-Identifier: Apache-2.0
"""
import hashlib
import json
from pathlib import Path, PurePosixPath
import sys
import zipfile

ROOT = Path(__file__).resolve().parent.parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def inventory(files):
    listed = set()
    for line in files['SHA256SUMS.txt'].decode().splitlines():
        expected, name = line.split('  ', 1)
        require(name in files and name != 'SHA256SUMS.txt', f'Invalid hash entry: {name}')
        require(name not in listed, f'Duplicate hash entry: {name}')
        require(digest(files[name]) == expected, f'Hash mismatch: {name}')
        listed.add(name)
    require(listed == set(files) - {'SHA256SUMS.txt'}, 'Incomplete checksum coverage')


def main():
    manifest = json.loads((ROOT / 'release-manifest.json').read_text())
    files = {p.name: p.read_bytes() for p in (ROOT / 'release').iterdir() if p.is_file()}
    require(set(files) == set(manifest['files']), 'Release file set changed')
    for name, expected in manifest['files'].items():
        require(digest(files[name]) == expected, f'Release changed: {name}')
    inventory(files)
    total = 0
    for name, info in manifest['archives'].items():
        with zipfile.ZipFile(ROOT / 'release' / name) as archive:
            require(archive.testzip() is None, f'Archive CRC failure: {name}')
            names = archive.namelist()
            require(len(names) == len(set(names)), 'Duplicate archive entries')
            for entry in names:
                path = PurePosixPath(entry)
                require(not path.is_absolute() and '\\' not in entry, f'Unsafe path: {entry}')
                require(not set(path.parts) & {'..', '.git', '.lake', '.DS_Store', '__pycache__', '__MACOSX'}, f'Unwanted path: {entry}')
            sources = {entry: archive.read(entry) for entry in names}
        inventory(sources)
        base = ROOT / info['directory']
        for entry, data in sources.items():
            target = base / entry
            require(target.is_file() and not target.is_symlink(), f'Missing regular source: {target}')
            require(target.read_bytes() == data, f'Extracted source mismatch: {target}')
        require(len(sources) == info['members'], f'Archive member count changed: {name}')
        total += len(sources)
    require((ROOT / 'LICENSES/Apache-2.0.txt').read_bytes() == (ROOT / 'sources/lean/LICENSE').read_bytes(), 'Apache license mismatch')
    journal = manifest['journal_pdf']
    require(digest((ROOT / journal['path']).read_bytes()) == journal['sha256'], 'Journal PDF mismatch')
    print(f'PASS: {len(files)} release files; {total} source members; complete hashes and exact source identity.')
    print('This is an integrity check, not a Lean build or theorem verification.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, zipfile.BadZipFile) as error:
        print(f'FAIL: {error}', file=sys.stderr)
        sys.exit(1)
