#!/usr/bin/env python3
"""Read-only byte-integrity check for the saved scientific completion record.

This verifies the manifest, not the mathematics. Use the separate proof
scripts to reproduce exact identities and interval certificates.
"""
from pathlib import Path
import hashlib
import json


def main():
    root = Path(__file__).resolve().parent
    manifest = json.loads((root/'science_completion_manifest.json').read_text())
    errors = []
    for item in manifest['files']:
        path = (root/item['path']).resolve()
        if not path.is_relative_to(root):
            errors.append({'path': item['path'], 'error': 'outside record directory'})
            continue
        if not path.is_file():
            errors.append({'path': item['path'], 'error': 'missing'})
            continue
        raw = path.read_bytes()
        if len(raw) != item['bytes']:
            errors.append({'path': item['path'], 'error': 'byte count differs'})
        if hashlib.sha256(raw).hexdigest() != item['sha256']:
            errors.append({'path': item['path'], 'error': 'SHA-256 differs'})
    print(json.dumps({'status': 'PASS' if not errors else 'FAIL',
                      'checked_files': len(manifest['files']), 'errors': errors,
                      'scope': 'Byte integrity only; see proof scripts and report for scientific verification.'}, indent=2))
    if errors:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
