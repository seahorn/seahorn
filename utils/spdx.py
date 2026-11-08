#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 The SeaHorn Authors
# SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

"""Check source SPDX headers and explicit REUSE coverage without rewriting notices.

Files licensed through REUSE.toml and LICENSES/ are exempt from inline headers.
All other tracked files must carry copyright and license tags in their leading
comment block (after a shebang). `reuse lint` validates the identifiers and texts.
Test fixtures are annotated in REUSE.toml to preserve diagnostic line numbers.
"""

import argparse
import fnmatch
import subprocess
import sys
import tomllib
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='check without modifying files')
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parent.parent)
    args = parser.parse_args()
    root = args.root.resolve()
    annotations = tomllib.loads((root / 'REUSE.toml').read_text()).get('annotations', [])
    patterns = []
    for annotation in annotations:
        paths = annotation['path']
        patterns.extend([paths] if isinstance(paths, str) else paths)
    files = subprocess.check_output(['git', '-C', str(root), 'ls-files', '-z']).decode().split('\0')
    bad = 0
    for name in filter(None, files):
        if name.startswith('LICENSES/') or any(fnmatch.fnmatchcase(name, p) for p in patterns):
            continue
        path = root / name
        if not path.exists():
            continue
        if path.is_symlink():
            print(f'{name}: annotate symlinks in REUSE.toml')
            bad += 1
            continue
        try:
            lines = path.read_text().splitlines()
        except UnicodeError:
            print(f'{name}: annotate binary files in REUSE.toml')
            bad += 1
            continue
        comments = []
        in_block = False
        for i, line in enumerate(lines):
            stripped = line.strip()
            if i == 0 and stripped.startswith('#!'):
                continue
            if not stripped:
                continue
            if stripped.startswith('/*'):
                in_block = True
            if not (in_block or stripped.startswith(('//', '#', ';', '*'))):
                break
            comments.append(stripped)
            if '*/' in stripped:
                in_block = False
        header = '\n'.join(comments)
        # Split tag literals so REUSE does not interpret them as this file's tags.
        for tag in ('SPDX-' + 'FileCopyrightText:', 'SPDX-' + 'License-Identifier:'):
            if tag not in header:
                print(f'{name}: missing leading {tag}')
                bad += 1
    print(f'spdx: {bad} problem(s)')
    return bool(bad)


if __name__ == '__main__':
    sys.exit(main())
