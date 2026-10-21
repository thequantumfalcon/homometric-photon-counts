"""Extract and verify all files embedded in the complete scientific record.

Usage:
  python extract_complete_science.py complete_record.pdf extracted_record

Requires pypdf. No scientific code is executed. The output directory must
be absent or empty. Manifest hashes establish byte integrity, not truth.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
from pypdf import PdfReader


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('pdf', type=Path)
    parser.add_argument('output_directory', type=Path)
    args = parser.parse_args()
    output = args.output_directory.resolve()
    if output.exists() and any(output.iterdir()):
        raise SystemExit('Refusing to overwrite a nonempty output directory.')
    reader = PdfReader(str(args.pdf))
    manifest_name = 'complete_science_manifest.json'
    records = reader.attachments
    if manifest_name not in records or len(records[manifest_name]) != 1:
        raise SystemExit('The unique complete-record manifest is missing.')
    manifest_bytes = records[manifest_name][0]
    manifest = json.loads(manifest_bytes)
    expected_names = {row['path'] for row in manifest['files']} | {manifest_name}
    if set(records) != expected_names:
        raise SystemExit('Attachment names do not match the manifest.')
    verified = {}
    for row in manifest['files']:
        name = row['path']
        relative = PurePosixPath(name)
        if relative.is_absolute() or '..' in relative.parts or '\\' in name:
            raise SystemExit('Unsafe attachment name.')
        values = records[name]
        if len(values) != 1:
            raise SystemExit('Duplicate attachment name: '+name)
        data = values[0]
        if len(data) != row['bytes'] or hashlib.sha256(data).hexdigest() != row['sha256']:
            raise SystemExit('Integrity check failed: '+name)
        target = (output / name).resolve()
        if not target.is_relative_to(output):
            raise SystemExit('Unsafe output location.')
        verified[name] = data
    output.mkdir(parents=True, exist_ok=True)
    for name, data in verified.items():
        target = output / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    (output / manifest_name).write_bytes(manifest_bytes)
    print(json.dumps({'status':'PASS','extracted_files':len(verified)+1,
                      'output_directory':str(output),
                      'scientific_scripts_executed':False}, indent=2))


if __name__ == '__main__':
    main()
