#!/usr/bin/env python3
"""Assemble and verify the complete portable scientific record.

Run ONLY after the final report, README, reviews, and visual QA are ready:

    python science_extension/assemble_complete_science.py --assemble

The extension report appears first, followed by the unchanged original report.
The original 44 proof files and original manifest are retained byte-for-byte.
Every current user-facing extension file is included except temporary files,
Python caches, the master manifest, and the self-referential verification file.

All attachment bytes and page content streams/text are checked before the
existing target PDF is atomically replaced. Its extended attributes are copied
to the new inode and checked, preserving its existing saved-file identity.
Named internal links are resolved to source-page destination arrays in memory
before merging. Every resulting internal link is verified against its original
source destination plus the report's page offset. Namespaced destination aliases
retain both reports' named targets without collisions. Original PDFs are never
modified; their embedded bytes remain identical to the source files.
The portable PDF is self-contained. External manifest and verification sidecars
are atomically committed immediately after the PDF; those separate renames are
not a multi-file filesystem transaction. No ZIP is created.

Requires pypdf. No scientific scripts are executed by this assembler.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
from hashlib import sha256
import io
import json
import os
from pathlib import Path, PurePosixPath
import stat
import tempfile

from pypdf import PdfReader, PdfWriter
from pypdf.generic import ArrayObject, IndirectObject, NameObject, TextStringObject

EXTENSION = Path(__file__).resolve().parent
WORKSPACE = EXTENSION.parent
ORIGINAL = WORKSPACE / "science_completion"
ORIGINAL_MANIFEST = ORIGINAL / "science_completion_manifest.json"
EXPECTED_ORIGINAL_MANIFEST_SHA256 = "3a23a6e6dafe93b6958c98d571befa061553d9bbe657409edaccf56d0bd753c0"
EXTENSION_REPORT = EXTENSION / "science_extension_report.pdf"
ORIGINAL_REPORT = ORIGINAL / "science_completion_report.pdf"
TARGET = ORIGINAL / "science_completion_complete_record.pdf"
MASTER_MANIFEST = EXTENSION / "complete_science_manifest.json"
VERIFICATION = EXTENSION / "portable_record_verification.json"
EMBEDDED_MANIFEST_NAME = "complete_science_manifest.json"
EXPECTED_ORIGINAL_FILES = 44


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(data):
    return sha256(data).hexdigest()


def canonical_json(value):
    return (json.dumps(value, indent=2, ensure_ascii=False)+"\n").encode("utf-8")


def safe_relative_name(name):
    require(isinstance(name, str) and bool(name), "An attachment path is empty or not text.")
    relative = PurePosixPath(name)
    require(not relative.is_absolute() and ".." not in relative.parts,
            "Unsafe relative path: "+name)
    require("\\" not in name and relative.as_posix() == name,
            "Noncanonical attachment path: "+name)
    return relative


def read_regular_file(path, root):
    """Reject symlinks and paths escaping the supplied source root."""
    relative = path.relative_to(root)
    current = root
    require(not root.is_symlink(), "Source root must not be a symlink: "+str(root))
    for part in relative.parts:
        current /= part
        require(not current.is_symlink(), "Symlink source refused: "+str(current))
    require(path.is_file(), "Missing regular source file: "+str(path))
    require(path.resolve().is_relative_to(root.resolve()), "Source escaped its root.")
    return path.read_bytes()


def excluded_extension_file(path):
    relative = path.relative_to(EXTENSION)
    if any(part == "__pycache__" or part.startswith("tmp_") or part.startswith(".")
           for part in relative.parts):
        return True
    if path in (MASTER_MANIFEST, VERIFICATION, TARGET):
        return True
    # These are compiler/editor by-products rather than user-facing sources.
    if path.suffix.lower() in {".pyc", ".pyo", ".aux", ".log", ".out", ".toc", ".fls", ".fdb_latexmk"}:
        return True
    if path.name.endswith((".synctex.gz", "~")):
        return True
    return False


def selected_extension_files():
    selected = []
    for path in EXTENSION.rglob("*"):
        if excluded_extension_file(path):
            continue
        if path.is_symlink():
            raise RuntimeError("User-facing extension symlink refused: "+str(path))
        if path.is_file():
            selected.append(path)
    return sorted(selected, key=lambda p: p.relative_to(WORKSPACE).as_posix())


def xattrs(path):
    require(hasattr(os, "listxattr") and hasattr(os, "getxattr") and hasattr(os, "setxattr"),
            "This platform cannot preserve the target's extended attributes.")
    return {name: os.getxattr(path, name) for name in os.listxattr(path)}


def stat_signature(path):
    value = path.stat()
    return (value.st_dev, value.st_ino, value.st_size, value.st_mtime_ns,
            value.st_mode, value.st_uid, value.st_gid)


def make_staged_file(directory, prefix, suffix, data):
    handle, name = tempfile.mkstemp(prefix=prefix, suffix=suffix, dir=directory)
    path = Path(name)
    try:
        with os.fdopen(handle, "wb") as stream:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
    except BaseException:
        path.unlink(missing_ok=True)
        raise
    return path


def page_content(page):
    contents = page.get_contents()
    return contents.get_data() if contents is not None else b""


def destination_array(reader, value):
    if isinstance(value, str):
        names = reader.named_destinations
        require(str(value) in names, "Unresolved internal named destination: "+str(value))
        return ArrayObject(names[str(value)].dest_array)
    array = value.get_object() if hasattr(value, "get_object") else value
    require(isinstance(array, ArrayObject) and len(array) >= 2, "Unsupported internal PDF destination.")
    return ArrayObject(array)


def page_index(reader, value):
    reference = value if isinstance(value, IndirectObject) else getattr(value, "indirect_reference", None)
    if reference is not None:
        for number, page in enumerate(reader.pages):
            candidate = page.indirect_reference
            if (candidate.idnum, candidate.generation) == (reference.idnum, reference.generation):
                return number
        raise RuntimeError("Internal PDF destination points outside its report.")
    require(isinstance(value, int) and 0 <= int(value) < len(reader.pages),
            "Unresolved internal PDF page target.")
    return int(value)


def annotation_inventory(reader):
    """Collect every internal link and external URI, preserving page order."""
    result = []
    for page in reader.pages:
        links = []
        for reference in page.get("/Annots", []):
            annotation = reference.get_object()
            if annotation.get("/Subtype") != "/Link":
                continue
            rectangle = tuple(str(x) for x in annotation.get("/Rect", []))
            value = annotation.get("/Dest")
            action = annotation.get("/A")
            action = action.get_object() if action is not None else None
            if value is None and action is not None and action.get("/S") == "/GoTo":
                value = action.get("/D")
            if value is not None:
                array = destination_array(reader, value)
                links.append({"kind": "internal", "target_page": page_index(reader, array[0]),
                              "destination_parameters": tuple(str(x) for x in array[1:]),
                              "rectangle": rectangle})
            elif action is not None and action.get("/S") == "/URI":
                links.append({"kind": "URI", "URI": str(action.get("/URI")), "rectangle": rectangle})
            else:
                raise RuntimeError("An unsupported link action requires review before assembly.")
        result.append(links)
    return result


def normalize_named_annotation_destinations(reader):
    """Mutate only this in-memory reader, never any source file."""
    converted = 0
    for page in reader.pages:
        for reference in page.get("/Annots", []):
            annotation = reference.get_object()
            if isinstance(annotation.get("/Dest"), str):
                annotation[NameObject("/Dest")] = destination_array(reader, annotation["/Dest"])
                converted += 1
            action = annotation.get("/A")
            action = action.get_object() if action is not None else None
            if action is not None and action.get("/S") == "/GoTo" and isinstance(action.get("/D"), str):
                action[NameObject("/D")] = destination_array(reader, action["/D"])
                converted += 1
    return converted


def append_reports(writer, inputs):
    """Append reports with collision-safe links and explicit named aliases."""
    converted = 0
    offset = 0
    for item in inputs:
        converted += normalize_named_annotation_destinations(item["reader"])
        writer.append(item["reader"], outline_item=item["outline_title"], import_outline=True)
        # Use a fresh source reader: append may resolve or cache destination
        # objects in the reader supplied to it. Destination aliases are explicit.
        fresh = PdfReader(io.BytesIO(item["bytes"]))
        for name, destination in fresh.named_destinations.items():
            array = ArrayObject(destination.dest_array)
            source_number = page_index(fresh, array[0])
            array[0] = writer.pages[offset+source_number].indirect_reference
            alias = item["destination_namespace"]+"::"+str(name)
            writer.add_named_destination_array(TextStringObject(alias), array)
        offset += len(fresh.pages)
    return converted


def verify_report_links(reader, inputs):
    actual = annotation_inventory(reader)
    actual_names = reader.named_destinations
    offset = 0
    total_internal = total_uris = total_aliases = 0
    rows = []
    for item in inputs:
        source = PdfReader(io.BytesIO(item["bytes"]))
        expected = annotation_inventory(source)
        internal = uris = 0
        for local_number, links in enumerate(expected):
            adjusted = []
            for link in links:
                corrected = dict(link)
                if link["kind"] == "internal":
                    corrected["target_page"] += offset
                    internal += 1
                else:
                    uris += 1
                adjusted.append(corrected)
            require(actual[offset+local_number] == adjusted,
                    f"Internal destination, URI, or link rectangle changed: {item['path']} page {local_number+1}")
        for name, destination in source.named_destinations.items():
            alias = item["destination_namespace"]+"::"+str(name)
            require(alias in actual_names, "Namespaced destination alias is missing: "+alias)
            wanted = destination.dest_array
            got = actual_names[alias].dest_array
            require(page_index(reader, got[0]) == offset+page_index(source, wanted[0]),
                    "Namespaced destination points to the wrong report: "+alias)
            require(tuple(str(x) for x in got[1:]) == tuple(str(x) for x in wanted[1:]),
                    "Namespaced destination coordinates changed: "+alias)
        aliases = len(source.named_destinations)
        rows.append({"source": item["path"], "internal_annotations_verified": internal,
                     "external_URI_annotations_verified": uris,
                     "named_destination_namespace": item["destination_namespace"],
                     "namespaced_destinations_verified": aliases})
        total_internal += internal
        total_uris += uris
        total_aliases += aliases
        offset += len(source.pages)
    return {"all_internal_annotation_targets_and_parameters_match_source_plus_page_offset": True,
            "all_external_URI_annotations_and_link_rectangles_preserved": True,
            "internal_annotations_verified": total_internal,
            "external_URI_annotations_verified": total_uris,
            "namespaced_destinations_verified": total_aliases,
            "source_reports": rows}


def verify_portable(pdf_bytes, inputs, attachments, manifest_bytes):
    reader = PdfReader(io.BytesIO(pdf_bytes))
    expected_pages = sum(len(item["reader"].pages) for item in inputs)
    require(len(reader.pages) == expected_pages, "Assembled page count mismatch.")
    page_rows = []
    offset = 0
    for item in inputs:
        # Re-open the untouched source bytes rather than comparing against a
        # reader that has participated in the writer's append operation.
        source = PdfReader(io.BytesIO(item["bytes"]))
        for local_number, source_page in enumerate(source.pages):
            output_page = reader.pages[offset+local_number]
            require(page_content(output_page) == page_content(source_page),
                    f"Page content stream changed: {item['path']} page {local_number+1}")
            require((output_page.extract_text() or "") == (source_page.extract_text() or ""),
                    f"Extracted page text changed: {item['path']} page {local_number+1}")
        page_rows.append({"source": item["path"], "source_sha256": digest(item["bytes"]),
                          "pages": len(source.pages), "first_assembled_page": offset+1,
                          "last_assembled_page": offset+len(source.pages)})
        offset += len(source.pages)
    expected = dict(attachments)
    expected[EMBEDDED_MANIFEST_NAME] = manifest_bytes
    records = reader.attachments
    require(set(records) == set(expected), "Embedded attachment names do not match the manifest.")
    for name, data in expected.items():
        blobs = records[name]
        require(len(blobs) == 1, "Duplicate embedded attachment: "+name)
        require(len(blobs[0]) == len(data) and digest(blobs[0]) == digest(data),
                "Embedded attachment integrity failure: "+name)
        require(blobs[0] == data, "Embedded attachment byte mismatch: "+name)
    # Match the extractor's manifest contract exactly.
    decoded_manifest = json.loads(records[EMBEDDED_MANIFEST_NAME][0])
    require({row["path"] for row in decoded_manifest["files"]} == set(attachments),
            "Manifest file set does not match embedded payloads.")
    for row in decoded_manifest["files"]:
        safe_relative_name(row["path"])
        data = records[row["path"]][0]
        require(len(data) == row["bytes"] and digest(data) == row["sha256"],
                "Manifest integrity mismatch: "+row["path"])
    link_audit = verify_report_links(reader, inputs)
    return expected_pages, len(expected), page_rows, link_audit


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--assemble", action="store_true",
                        help="Explicitly assemble after final source and visual QA approval.")
    args = parser.parse_args()
    require(args.assemble, "No write performed. Use --assemble only after the final report and record are ready.")
    require(TARGET.is_file() and not TARGET.is_symlink(), "The existing target PDF is missing or is a symlink.")
    target_signature = stat_signature(TARGET)
    target_bytes = TARGET.read_bytes()
    previous_target_hash = digest(target_bytes)
    target_attributes = xattrs(TARGET)

    original_manifest_bytes = read_regular_file(ORIGINAL_MANIFEST, ORIGINAL)
    require(digest(original_manifest_bytes) == EXPECTED_ORIGINAL_MANIFEST_SHA256,
            "The original manifest changed; refusing to redefine the preserved proof record.")
    original_manifest = json.loads(original_manifest_bytes)
    old_rows = original_manifest["files"]
    require(original_manifest["file_count"] == len(old_rows) == EXPECTED_ORIGINAL_FILES,
            "The original manifest must identify exactly 44 files.")
    require(len({row["path"] for row in old_rows}) == len(old_rows), "Original manifest has duplicate paths.")

    attachments = {}
    snapshots = {}
    preserved_rows = []
    for row in old_rows:
        relative = safe_relative_name(row["path"])
        source = ORIGINAL.joinpath(*relative.parts)
        data = read_regular_file(source, ORIGINAL)
        require(len(data) == row["bytes"] and digest(data) == row["sha256"],
                "An original proof file changed: "+row["path"])
        name = "science_completion/"+row["path"]
        attachments[name] = data
        snapshots[source] = data
        preserved_rows.append({"path": name, "bytes": row["bytes"], "sha256": row["sha256"]})
    require(sum(row["bytes"] for row in old_rows) == original_manifest["total_bytes"],
            "Original manifest byte total mismatch.")
    attachments["science_completion/"+ORIGINAL_MANIFEST.name] = original_manifest_bytes
    snapshots[ORIGINAL_MANIFEST] = original_manifest_bytes

    extension_paths = selected_extension_files()
    require(EXTENSION_REPORT in extension_paths, "The final extension report is not ready.")
    require(EXTENSION/"extract_complete_science.py" in extension_paths, "The complete-record extraction helper is missing.")
    for source in extension_paths:
        name = source.relative_to(WORKSPACE).as_posix()
        safe_relative_name(name)
        require(name not in attachments, "Duplicate payload name: "+name)
        data = read_regular_file(source, EXTENSION)
        attachments[name] = data
        snapshots[source] = data
    attachments = dict(sorted(attachments.items()))
    assembled_at = datetime.now(timezone.utc).isoformat()
    manifest = {
        "schema": "complete-scientific-proof-record-v1", "date": "2026-10-20",
        "assembled_at_utc": assembled_at,
        "file_count": len(attachments), "total_bytes": sum(map(len, attachments.values())),
        "scope": "Complete original and extension proof payloads. This master manifest, the portable container, and its self-referential verification sidecar are excluded from self-hashing. Hashes establish byte identity, not scientific truth.",
        "original_manifest_sha256": EXPECTED_ORIGINAL_MANIFEST_SHA256,
        "original_files_preserved": EXPECTED_ORIGINAL_FILES,
        "original_manifest_embedded_as": "science_completion/"+ORIGINAL_MANIFEST.name,
        "extension_files_included": len(extension_paths),
        "readable_page_order": ["science_extension/science_extension_report.pdf", "science_completion/science_completion_report.pdf"],
        "files": [{"path": name, "bytes": len(data), "sha256": digest(data)}
                  for name, data in attachments.items()],
    }
    manifest_bytes = canonical_json(manifest)
    input_paths = [EXTENSION_REPORT, ORIGINAL_REPORT]
    inputs = [{"path": p.relative_to(WORKSPACE).as_posix(), "bytes": snapshots[p],
               "reader": PdfReader(io.BytesIO(snapshots[p])), "destination_namespace": namespace,
               "outline_title": title}
              for p, namespace, title in zip(input_paths, ["extension", "foundation"],
                                             ["Extension report", "Original completed proof report"])]
    require(all(not item["reader"].is_encrypted for item in inputs), "Input report is encrypted.")
    require(len(inputs[1]["reader"].pages) == 18, "The unchanged original report must have 18 pages.")

    writer = PdfWriter()
    normalized_links = append_reports(writer, inputs)
    writer.add_metadata({"/Title": "Complete scientific proof record: further results and original proofs",
                         "/Subject": "Extension report followed by original report, with all original and new reproducibility files embedded.",
                         "/Keywords": "homometry; exact proofs; phase laws; photon counting; reproducibility"})
    for name, data in attachments.items():
        writer.add_attachment(name, data)
    writer.add_attachment(EMBEDDED_MANIFEST_NAME, manifest_bytes)
    buffer = io.BytesIO()
    writer.write(buffer)
    pdf_bytes = buffer.getvalue()
    pages, attachment_count, page_rows, link_audit = verify_portable(pdf_bytes, inputs, attachments, manifest_bytes)

    verification = {
        "status": "PASS", "assembled_at_utc": assembled_at,
        "record_file": str(TARGET.relative_to(WORKSPACE)), "record_bytes": len(pdf_bytes),
        "record_sha256": digest(pdf_bytes), "previous_portable_record_sha256": previous_target_hash,
        "master_manifest_sha256": digest(manifest_bytes),
        "assembler_sha256": digest(Path(__file__).read_bytes()),
        "pages": pages, "input_reports_in_order": page_rows,
        "embedded_file_count_including_master_manifest": attachment_count,
        "payload_files_in_master_manifest": len(attachments),
        "original_manifest_sha256": EXPECTED_ORIGINAL_MANIFEST_SHA256,
        "all_44_original_file_lengths_and_SHA256_unchanged": True,
        "original_manifest_embedded_byte_for_byte": True,
        "original_files_verified": preserved_rows,
        "every_page_content_stream_and_extracted_text_identical_to_its_input_report": True,
        "internal_link_collision_repair": {
            "method": "Resolve named internal annotation destinations to explicit source-page arrays in memory before merging; pypdf then remaps page references. Preserve each report's named destinations under unique extension:: and foundation:: namespaces.",
            "named_annotation_destinations_normalized": normalized_links,
            "original_PDF_bytes_unchanged": True,
            "verification": link_audit,
        },
        "every_attachment_reextracted_and_byte_length_and_SHA256_verified": True,
        "source_files_rechecked_before_atomic_commit": True,
        "existing_target_extended_attributes_preserved": True,
        "PDF_replacement_method": "Verified same-directory staged file, existing metadata copied, then atomic os.replace.",
        "rolling_ZIP_created_or_updated": False,
        "scope": "Assembly, page equivalence, and byte integrity. Mathematical correctness, source review, and visual QA are documented in the included proof and review files.",
    }
    staged = []
    installed = False
    try:
        pdf_stage = make_staged_file(TARGET.parent, "tmp_complete_science_", ".pdf", pdf_bytes)
        staged.append(pdf_stage)
        original_stat = TARGET.stat()
        os.chmod(pdf_stage, stat.S_IMODE(original_stat.st_mode))
        staged_stat = pdf_stage.stat()
        if (staged_stat.st_uid, staged_stat.st_gid) != (original_stat.st_uid, original_stat.st_gid):
            os.chown(pdf_stage, original_stat.st_uid, original_stat.st_gid)
        for name, value in target_attributes.items():
            os.setxattr(pdf_stage, name, value)
        require(xattrs(pdf_stage) == target_attributes, "Existing target attributes were not preserved on the staged PDF.")
        require(pdf_stage.read_bytes() == pdf_bytes, "Staged PDF bytes differ from the verified buffer.")
        manifest_stage = make_staged_file(EXTENSION, "tmp_complete_manifest_", ".json", manifest_bytes)
        staged.append(manifest_stage)
        verification_stage = make_staged_file(EXTENSION, "tmp_portable_verification_", ".json", canonical_json(verification))
        staged.append(verification_stage)

        # Abort on a concurrent source change instead of silently assembling a
        # mixture of versions. The manifest and verification outputs are excluded.
        require(selected_extension_files() == extension_paths,
                "The user-facing extension file inventory changed during assembly.")
        for source, data in snapshots.items():
            root = ORIGINAL if source.is_relative_to(ORIGINAL) else EXTENSION
            require(read_regular_file(source, root) == data, "A source changed during assembly: "+str(source))
        require(stat_signature(TARGET) == target_signature and digest(TARGET.read_bytes()) == previous_target_hash,
                "The target PDF changed during assembly; refusing to overwrite it.")
        require(xattrs(TARGET) == target_attributes, "The saved-file identity changed during assembly.")

        # This atomic rename is the only operation that replaces the old PDF.
        # Everything above can fail while leaving its existing bytes intact.
        os.replace(pdf_stage, TARGET)
        installed = True
        os.replace(manifest_stage, MASTER_MANIFEST)
        os.replace(verification_stage, VERIFICATION)
        for directory in {TARGET.parent, EXTENSION}:
            descriptor = os.open(directory, os.O_RDONLY | os.O_DIRECTORY)
            try:
                os.fsync(descriptor)
            finally:
                os.close(descriptor)
    except BaseException as exc:
        if installed:
            raise RuntimeError("The verified self-contained PDF was atomically installed, but a sidecar or directory-sync operation failed. Inspect the target before retrying; the old target was already replaced.") from exc
        raise
    finally:
        for path in staged:
            path.unlink(missing_ok=True)
    print(json.dumps({"status": "PASS", "output": str(TARGET),
                      "record_sha256": verification["record_sha256"], "record_bytes": len(pdf_bytes),
                      "pages": pages, "attachments": attachment_count,
                      "original_files_preserved": EXPECTED_ORIGINAL_FILES,
                      "original_manifest_preserved": True,
                      "extension_files_included": len(extension_paths),
                      "manifest": str(MASTER_MANIFEST), "verification": str(VERIFICATION),
                      "ZIP_created_or_updated": False}, indent=2))


if __name__ == "__main__":
    main()
