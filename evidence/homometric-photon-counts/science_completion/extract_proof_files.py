#!/usr/bin/env python3
"""Extract and verify the files embedded in science_completion_complete_record.pdf.

Requires the pypdf package. A PDF reader with an attachments panel can also
extract the files. This helper does not execute the extracted proof scripts.
Usage: python extract_proof_files.py [record.pdf] [new_output_directory]
"""
from pathlib import Path, PurePosixPath
import hashlib
import json
import sys


def main():
    from pypdf import PdfReader
    pdf = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).with_name('science_completion_complete_record.pdf')
    destination = (Path(sys.argv[2]) if len(sys.argv) > 2 else Path('extracted_science_completion')).resolve()
    if destination.exists() and any(destination.iterdir()):
        raise SystemExit('Choose a new or empty output directory; existing files will not be overwritten.')
    reader = PdfReader(str(pdf))
    payloads = {}
    for name, values in reader.attachments.items():
        rel = PurePosixPath(name)
        if rel.is_absolute() or '..' in rel.parts or not rel.parts:
            raise SystemExit('Invalid attachment path: '+name)
        if len(values) != 1:
            raise SystemExit('Duplicate attachment name: '+name)
        payloads[name] = values[0]
    manifest = json.loads(payloads['science_completion_manifest.json'])
    expected_names = {item['path'] for item in manifest['files']} | {'science_completion_manifest.json'}
    if set(payloads) != expected_names:
        raise SystemExit('Attachment names do not exactly match the manifest.')
    for item in manifest['files']:
        raw = payloads[item['path']]
        if len(raw) != item['bytes'] or hashlib.sha256(raw).hexdigest() != item['sha256']:
            raise SystemExit('Integrity check failed: '+item['path'])
    destination.mkdir(parents=True, exist_ok=True)
    for name, raw in payloads.items():
        path = destination/name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)
    print(json.dumps({'status': 'PASS', 'files_extracted': len(payloads),
                      'directory': str(destination),
                      'scope': 'All embedded file bytes verified. No proof code was executed.'}, indent=2))


if __name__ == '__main__':
    main()
