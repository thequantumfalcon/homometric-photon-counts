#!/usr/bin/env python3
"""Preserve the complete predecessor record and add the advance results.

Do not run final assembly until the advance report, README, reviews, and
visual QA are ready. The sole writing entry point is:

    python science_advance/assemble_complete_science.py --assemble

Preservation strategy
---------------------
The pinned science_frontier/complete_science_manifest.json is immutable. Its
125 named payloads are the authoritative predecessor inventory: each source
must still match its recorded byte length and SHA256. These 125 byte strings
are embedded unchanged, and that exact predecessor manifest becomes an
additional payload named science_frontier/complete_science_manifest.json.
No predecessor source or manifest is rewritten. In particular, the preserved
extension assembler remains among those 125 payloads.

All current user-facing science_advance files are added, excluding tmp_*
paths, hidden/cache/compiler artifacts, the new master manifest, and the
self-referential portable verification sidecar. The new master sidecar is
science_advance/complete_science_manifest.json. Its embedded name remains
complete_science_manifest.json, preserving the existing extractor contract.
The new advance report comes first, then the unchanged 13-page frontier,
13-page extension, and 18-page foundation reports.

The verified predecessor assembler is loaded through importlib, reusing its
page, link, attachment, xattr, staging, and integrity utilities. The four
report destination namespaces are advance::, frontier::, extension::, and
foundation::.
Every embedded byte string, page content stream, extracted page text, internal
link target, URI, link rectangle, and namespaced destination is checked before
commit. All source bytes and the source inventory are rechecked before the
atomic replacement of science_completion/science_completion_complete_record.pdf.
Its existing extended attributes and mode/owner are preserved on the new inode.

The PDF is self-contained. Its two new sidecars are atomically renamed after
the PDF; these separate renames are not a multi-file filesystem transaction.
No ZIP is created and no scientific producer is executed. Importing this
module or asking for --help does not assemble or modify the record.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
from hashlib import sha256
import importlib.util
import io
import json
import os
from pathlib import Path
import stat
import sys

from pypdf import PdfReader, PdfWriter

ADVANCE = Path(__file__).resolve().parent
WORKSPACE = ADVANCE.parent
FRONTIER = WORKSPACE / "science_frontier"
EXTENSION = WORKSPACE / "science_extension"
FOUNDATION = WORKSPACE / "science_completion"
PREDECESSOR_MANIFEST = FRONTIER / "complete_science_manifest.json"
EXPECTED_PREDECESSOR_MANIFEST_SHA256 = "15dc6eafac0d2f2d3cb87d526170aa49b8ebec136f3c93e75ad8e08e6fc305ee"
EXPECTED_PREDECESSOR_FILES = 125
PREDECESSOR_ASSEMBLER = EXTENSION / "assemble_complete_science.py"
PREDECESSOR_MANIFEST_PAYLOAD = "science_frontier/complete_science_manifest.json"
ADVANCE_REPORT = ADVANCE / "science_advance_report.pdf"
FRONTIER_REPORT = FRONTIER / "science_frontier_report.pdf"
EXTENSION_REPORT = EXTENSION / "science_extension_report.pdf"
FOUNDATION_REPORT = FOUNDATION / "science_completion_report.pdf"
TARGET = FOUNDATION / "science_completion_complete_record.pdf"
MASTER_MANIFEST = ADVANCE / "complete_science_manifest.json"
VERIFICATION = ADVANCE / "portable_record_verification.json"
EMBEDDED_MANIFEST_NAME = "complete_science_manifest.json"


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def bootstrap_read(path):
    """Check source paths before the pinned predecessor utility is imported."""
    relative = path.relative_to(WORKSPACE)
    current = WORKSPACE
    require(not current.is_symlink(), "The workspace must not be a symlink.")
    for part in relative.parts:
        current /= part
        require(not current.is_symlink(), "Symlink source refused: "+str(current))
    require(path.is_file(), "Missing source file: "+str(path))
    require(path.resolve().is_relative_to(WORKSPACE.resolve()), "Source escaped the workspace.")
    return path.read_bytes()


def load_predecessor_utilities():
    """Pin the old manifest and utility bytes before importing its functions."""
    manifest_bytes = bootstrap_read(PREDECESSOR_MANIFEST)
    require(sha256(manifest_bytes).hexdigest() == EXPECTED_PREDECESSOR_MANIFEST_SHA256,
            "The predecessor manifest changed; refusing to redefine its preserved record.")
    manifest = json.loads(manifest_bytes)
    rows = manifest["files"]
    require(manifest["file_count"] == len(rows) == EXPECTED_PREDECESSOR_FILES,
            "The pinned predecessor manifest must identify exactly 125 payloads.")
    require(len({row["path"] for row in rows}) == len(rows),
            "Duplicate paths in the predecessor manifest.")
    utility_name = PREDECESSOR_ASSEMBLER.relative_to(WORKSPACE).as_posix()
    utility_rows = [row for row in rows if row["path"] == utility_name]
    require(len(utility_rows) == 1, "The preserved assembler is missing from its manifest.")
    utility_bytes = bootstrap_read(PREDECESSOR_ASSEMBLER)
    row = utility_rows[0]
    require(len(utility_bytes) == row["bytes"] and sha256(utility_bytes).hexdigest() == row["sha256"],
            "The predecessor assembler changed; refusing to import unpinned utilities.")
    spec = importlib.util.spec_from_file_location("preserved_science_extension_assembler",
                                                 PREDECESSOR_ASSEMBLER)
    require(spec is not None and spec.loader is not None, "Cannot import predecessor utilities.")
    utilities = importlib.util.module_from_spec(spec)
    previous_bytecode_setting = sys.dont_write_bytecode
    try:
        # Import the preserved source without creating/updating a cache inside
        # the predecessor directory. The module's guarded main is not invoked.
        sys.dont_write_bytecode = True
        spec.loader.exec_module(utilities)
    finally:
        sys.dont_write_bytecode = previous_bytecode_setting
    require(bootstrap_read(PREDECESSOR_ASSEMBLER) == utility_bytes,
            "The predecessor assembler changed while its utilities were being imported.")
    require(utilities.EMBEDDED_MANIFEST_NAME == EMBEDDED_MANIFEST_NAME,
            "The preserved portable verifier has an incompatible manifest contract.")
    return utilities, manifest_bytes, manifest


def load_preserved_payloads(utilities, manifest_bytes, manifest):
    """Read-only validation of every predecessor payload against its old row."""
    attachments = {}
    snapshots = {PREDECESSOR_MANIFEST: manifest_bytes}
    old_rows = manifest["files"]
    require(sum(row["bytes"] for row in old_rows) == manifest["total_bytes"],
            "Predecessor manifest byte total mismatch.")
    for row in old_rows:
        relative = utilities.safe_relative_name(row["path"])
        require(relative.parts[0] in {"science_completion", "science_extension", "science_frontier"},
                "Unexpected predecessor payload namespace: "+row["path"])
        source = WORKSPACE.joinpath(*relative.parts)
        data = utilities.read_regular_file(source, WORKSPACE)
        require(len(data) == row["bytes"] and utilities.digest(data) == row["sha256"],
                "A predecessor proof file changed: "+row["path"])
        attachments[row["path"]] = data
        snapshots[source] = data
    require(len(attachments) == EXPECTED_PREDECESSOR_FILES,
            "Predecessor payload count changed during validation.")
    require(PREDECESSOR_MANIFEST_PAYLOAD not in attachments,
            "The predecessor manifest unexpectedly names itself as a payload.")
    attachments[PREDECESSOR_MANIFEST_PAYLOAD] = manifest_bytes
    return attachments, snapshots


def excluded_advance_file(path):
    relative = path.relative_to(ADVANCE)
    if any(part == "__pycache__" or part.startswith("tmp_") or part.startswith(".")
           for part in relative.parts):
        return True
    if path in (MASTER_MANIFEST, VERIFICATION):
        return True
    if path.suffix.lower() in {".pyc", ".pyo", ".aux", ".log", ".out", ".toc",
                               ".fls", ".fdb_latexmk"}:
        return True
    return path.name.endswith((".synctex.gz", "~"))


def selected_advance_files():
    selected = []
    for path in ADVANCE.rglob("*"):
        if excluded_advance_file(path):
            continue
        require(not path.is_symlink(), "User-facing advance symlink refused: "+str(path))
        if path.is_file():
            selected.append(path)
    return sorted(selected, key=lambda p: p.relative_to(WORKSPACE).as_posix())


def verify_predecessor_in_existing_record(target_bytes, attachments, manifest_bytes):
    """Ensure that the old portable bytes agree with the preserved sources.

    Accept the predecessor's old root manifest or its namespaced copy from a
    previous advance assembly, allowing a later reviewed rebuild.
    """
    reader = PdfReader(io.BytesIO(target_bytes))
    require(not reader.is_encrypted, "The existing portable record is encrypted.")
    records = reader.attachments
    for name, data in attachments.items():
        if name == PREDECESSOR_MANIFEST_PAYLOAD:
            continue
        require(name in records and len(records[name]) == 1 and records[name][0] == data,
                "Existing portable predecessor payload differs or is missing: "+name)
    possible_names = (PREDECESSOR_MANIFEST_PAYLOAD, EMBEDDED_MANIFEST_NAME)
    require(any(name in records and len(records[name]) == 1 and
                records[name][0] == manifest_bytes for name in possible_names),
            "The exact predecessor master manifest is missing from the existing portable record.")


def verify_preserved_reports_in_existing_record(utilities, target_bytes, inputs):
    """Verify the old 44-page suffix, including links, before any replacement.

    The suffix stays the same on a later reviewed rebuild that already has
    an advance report in front. Offsets are measured in the current target;
    no previous PDF page or annotation object is mutated by this check.
    """
    reader = PdfReader(io.BytesIO(target_bytes))
    expected_pages = sum(len(item["reader"].pages) for item in inputs)
    require(expected_pages == 44, "The three preserved reports must total 44 pages.")
    require(len(reader.pages) >= expected_pages,
            "The existing portable record is too short for the preserved reports.")
    offset = len(reader.pages)-expected_pages
    suffix_start = offset
    actual_links = utilities.annotation_inventory(reader)
    actual_names = reader.named_destinations
    rows = []
    for item in inputs:
        source = PdfReader(io.BytesIO(item["bytes"]))
        expected_links = utilities.annotation_inventory(source)
        internal = uris = 0
        for number, page in enumerate(source.pages):
            existing_page = reader.pages[offset+number]
            require(utilities.page_content(existing_page) == utilities.page_content(page),
                    "Existing predecessor page content differs: "+item["path"])
            require((existing_page.extract_text() or "") == (page.extract_text() or ""),
                    "Existing predecessor page text differs: "+item["path"])
            adjusted = []
            for link in expected_links[number]:
                adjusted_link = dict(link)
                if link["kind"] == "internal":
                    adjusted_link["target_page"] += offset
                    internal += 1
                else:
                    uris += 1
                adjusted.append(adjusted_link)
            require(actual_links[offset+number] == adjusted,
                    "Existing predecessor link target, URI, or rectangle differs: "+item["path"])
        for name, destination in source.named_destinations.items():
            alias = item["destination_namespace"]+"::"+str(name)
            require(alias in actual_names,
                    "Existing predecessor destination alias is missing: "+alias)
            wanted, got = destination.dest_array, actual_names[alias].dest_array
            require(utilities.page_index(reader, got[0]) == offset+utilities.page_index(source, wanted[0]),
                    "Existing predecessor destination page differs: "+alias)
            require(tuple(str(x) for x in got[1:]) == tuple(str(x) for x in wanted[1:]),
                    "Existing predecessor destination parameters differ: "+alias)
        rows.append({"source": item["path"], "pages": len(source.pages),
                     "source_sha256": utilities.digest(item["bytes"]),
                     "first_existing_page": offset+1,
                     "last_existing_page": offset+len(source.pages),
                     "internal_links_verified": internal, "external_URI_links_verified": uris,
                     "namespaced_destinations_verified": len(source.named_destinations)})
        offset += len(source.pages)
    require(offset == len(reader.pages), "Preserved-report suffix coverage failed.")
    return {"status": "PASS", "preserved_pages": expected_pages,
            "first_existing_page": suffix_start+1, "last_existing_page": offset,
            "content_streams_text_annotations_and_destination_aliases_unchanged": True,
            "source_reports": rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--assemble", action="store_true",
                        help="Assemble only after the final advance sources and visual QA are ready.")
    args = parser.parse_args()
    require(args.assemble, "No write performed. Use --assemble only after the final report and record are ready.")

    utilities, predecessor_bytes, predecessor = load_predecessor_utilities()
    require(TARGET.is_file() and not TARGET.is_symlink(),
            "The existing target PDF is missing or is a symlink.")
    target_signature = utilities.stat_signature(TARGET)
    target_bytes = TARGET.read_bytes()
    previous_target_hash = utilities.digest(target_bytes)
    target_attributes = utilities.xattrs(TARGET)

    attachments, snapshots = load_preserved_payloads(utilities, predecessor_bytes, predecessor)
    verify_predecessor_in_existing_record(target_bytes, attachments, predecessor_bytes)
    advance_paths = selected_advance_files()
    require(ADVANCE_REPORT in advance_paths, "The final advance report is not ready.")
    require(Path(__file__).resolve() in advance_paths, "The advance assembler must be a new payload.")
    require("science_extension/extract_complete_science.py" in attachments,
            "The preserved complete-record extraction helper is missing.")
    for source in advance_paths:
        name = source.relative_to(WORKSPACE).as_posix()
        utilities.safe_relative_name(name)
        require(name not in attachments, "Duplicate payload name: "+name)
        data = utilities.read_regular_file(source, ADVANCE)
        attachments[name] = data
        snapshots[source] = data
    attachments = dict(sorted(attachments.items()))
    require(len(attachments) == EXPECTED_PREDECESSOR_FILES+1+len(advance_paths),
            "Preserved and advance payload counts do not add up.")

    report_paths = [ADVANCE_REPORT, FRONTIER_REPORT, EXTENSION_REPORT, FOUNDATION_REPORT]
    namespaces = ["advance", "frontier", "extension", "foundation"]
    titles = ["Latest mathematical advances and proof status", "Preserved frontier report", "Preserved extension report",
              "Preserved original completed proof report"]
    inputs = [{"path": p.relative_to(WORKSPACE).as_posix(), "bytes": snapshots[p],
               "reader": PdfReader(io.BytesIO(snapshots[p])),
               "destination_namespace": namespace, "outline_title": title}
              for p, namespace, title in zip(report_paths, namespaces, titles)]
    require(all(not item["reader"].is_encrypted for item in inputs), "An input report is encrypted.")
    require(len(inputs[0]["reader"].pages) > 0, "The advance report has no pages.")
    require(len(inputs[1]["reader"].pages) == 13, "The unchanged frontier report must have 13 pages.")
    require(len(inputs[2]["reader"].pages) == 13, "The unchanged extension report must have 13 pages.")
    require(len(inputs[3]["reader"].pages) == 18, "The unchanged foundation report must have 18 pages.")
    existing_report_audit = verify_preserved_reports_in_existing_record(
        utilities, target_bytes, inputs[1:])

    assembled_at = datetime.now(timezone.utc).isoformat()
    manifest = {
        "schema": "complete-scientific-proof-record-v3",
        "date": "2026-10-21", "assembled_at_utc": assembled_at,
        "file_count": len(attachments), "total_bytes": sum(map(len, attachments.values())),
        "scope": "Complete preserved foundation, extension, and frontier payloads, their unchanged manifests, and new advance proof payloads. This active master, the portable container, and the self-referential verification sidecar are excluded from self-hashing. Hashes establish byte identity, not scientific truth.",
        "preservation_strategy": "Keep every predecessor manifest row and corresponding payload byte-for-byte, embed the exact predecessor master under its science_frontier path, and add the current user-facing advance inventory without editing old sources.",
        "predecessor_manifest_sha256": EXPECTED_PREDECESSOR_MANIFEST_SHA256,
        "predecessor_payload_files_preserved": EXPECTED_PREDECESSOR_FILES,
        "predecessor_manifest_embedded_as": PREDECESSOR_MANIFEST_PAYLOAD,
        "original_manifest_sha256": predecessor["original_manifest_sha256"],
        "original_files_preserved": predecessor["original_files_preserved"],
        "original_manifest_embedded_as": predecessor["original_manifest_embedded_as"],
        "advance_files_included": len(advance_paths),
        "master_manifest_sidecar": MASTER_MANIFEST.relative_to(WORKSPACE).as_posix(),
        "embedded_master_manifest_name": EMBEDDED_MANIFEST_NAME,
        "readable_page_order": [p.relative_to(WORKSPACE).as_posix() for p in report_paths],
        "files": [{"path": name, "bytes": len(data), "sha256": utilities.digest(data)}
                  for name, data in attachments.items()],
    }
    manifest_bytes = utilities.canonical_json(manifest)
    row_by_name = {row["path"]: row for row in manifest["files"]}
    require(all(row_by_name[row["path"]] == row for row in predecessor["files"]),
            "A predecessor manifest row changed in the new active inventory.")

    writer = PdfWriter()
    normalized_links = utilities.append_reports(writer, inputs)
    writer.add_metadata({
        "/Title": "Complete scientific proof record: latest advances and preserved proofs",
        "/Subject": "Advance report, preserved frontier report, preserved extension report, and preserved foundation report, with every predecessor and new reproducibility payload embedded.",
        "/Keywords": "homometry; exact proofs; photon counting; finite samples; calibration; reproducibility",
    })
    for name, data in attachments.items():
        writer.add_attachment(name, data)
    writer.add_attachment(EMBEDDED_MANIFEST_NAME, manifest_bytes)
    buffer = io.BytesIO()
    writer.write(buffer)
    pdf_bytes = buffer.getvalue()
    pages, attachment_count, page_rows, link_audit = utilities.verify_portable(
        pdf_bytes, inputs, attachments, manifest_bytes)

    verification = {
        "status": "PASS", "assembled_at_utc": assembled_at,
        "record_file": TARGET.relative_to(WORKSPACE).as_posix(),
        "record_bytes": len(pdf_bytes), "record_sha256": utilities.digest(pdf_bytes),
        "previous_portable_record_sha256": previous_target_hash,
        "master_manifest_sha256": utilities.digest(manifest_bytes),
        "master_manifest_sidecar": MASTER_MANIFEST.relative_to(WORKSPACE).as_posix(),
        "assembler_sha256": utilities.digest(snapshots[Path(__file__).resolve()]),
        "preserved_assembler_utilities_sha256": utilities.digest(snapshots[PREDECESSOR_ASSEMBLER]),
        "predecessor_manifest_sha256": EXPECTED_PREDECESSOR_MANIFEST_SHA256,
        "predecessor_payload_files_preserved": EXPECTED_PREDECESSOR_FILES,
        "all_125_predecessor_payload_lengths_SHA256_and_bytes_unchanged": True,
        "predecessor_manifest_embedded_byte_for_byte": True,
        "predecessor_manifest_embedded_as": PREDECESSOR_MANIFEST_PAYLOAD,
        "predecessor_payloads_matched_existing_portable_record": True,
        "predecessor_readable_pages_and_links_matched_existing_portable_record": existing_report_audit,
        "predecessor_manifest_rows_preserved_exactly": True,
        "predecessor_files_verified": predecessor["files"],
        "advance_files_included": len(advance_paths),
        "pages": pages, "input_reports_in_order": page_rows,
        "embedded_file_count_including_master_manifest": attachment_count,
        "payload_files_in_master_manifest": len(attachments),
        "every_page_content_stream_and_extracted_text_identical_to_its_input_report": True,
        "internal_link_collision_repair": {
            "method": "Use the pinned predecessor utilities: resolve named internal annotation destinations to explicit source-page arrays before merging; preserve named targets under advance::, frontier::, extension::, and foundation:: aliases.",
            "named_annotation_destinations_normalized": normalized_links,
            "original_PDF_bytes_unchanged": True, "verification": link_audit,
        },
        "every_attachment_reextracted_and_byte_length_and_SHA256_verified": True,
        "source_files_and_advance_inventory_rechecked_before_atomic_commit": True,
        "existing_target_extended_attributes_preserved": True,
        "PDF_replacement_method": "Verified same-directory staged file, existing mode/owner and extended attributes copied, then atomic os.replace.",
        "rolling_ZIP_created_or_updated": False,
        "scientific_producers_executed": False,
        "scope": "Assembly, predecessor preservation, page/link equivalence, and byte integrity. Scientific correctness, source review, and visual QA are documented in the included proof and review files.",
    }

    staged = []
    installed = False
    try:
        pdf_stage = utilities.make_staged_file(TARGET.parent, "tmp_advance_complete_", ".pdf", pdf_bytes)
        staged.append(pdf_stage)
        target_stat = TARGET.stat()
        os.chmod(pdf_stage, stat.S_IMODE(target_stat.st_mode))
        stage_stat = pdf_stage.stat()
        if (stage_stat.st_uid, stage_stat.st_gid) != (target_stat.st_uid, target_stat.st_gid):
            os.chown(pdf_stage, target_stat.st_uid, target_stat.st_gid)
        for name, value in target_attributes.items():
            os.setxattr(pdf_stage, name, value)
        require(utilities.xattrs(pdf_stage) == target_attributes,
                "The existing target's extended attributes were not preserved on the staged PDF.")
        require(pdf_stage.read_bytes() == pdf_bytes, "Staged PDF bytes differ from the verified buffer.")
        manifest_stage = utilities.make_staged_file(ADVANCE, "tmp_advance_manifest_", ".json", manifest_bytes)
        staged.append(manifest_stage)
        verification_stage = utilities.make_staged_file(
            ADVANCE, "tmp_advance_verification_", ".json", utilities.canonical_json(verification))
        staged.append(verification_stage)

        require(selected_advance_files() == advance_paths,
                "The user-facing advance inventory changed during assembly.")
        for source, data in snapshots.items():
            require(utilities.read_regular_file(source, WORKSPACE) == data,
                    "A preserved or new source changed during assembly: "+str(source))
        require(utilities.stat_signature(TARGET) == target_signature and
                utilities.digest(TARGET.read_bytes()) == previous_target_hash,
                "The target PDF changed during assembly; refusing to overwrite it.")
        require(utilities.xattrs(TARGET) == target_attributes,
                "The saved-file identity changed during assembly.")

        # Only this final atomic rename replaces the existing portable record.
        # All verification above can fail without altering its existing bytes.
        os.replace(pdf_stage, TARGET)
        installed = True
        os.replace(manifest_stage, MASTER_MANIFEST)
        os.replace(verification_stage, VERIFICATION)
        for directory in {TARGET.parent, ADVANCE}:
            descriptor = os.open(directory, os.O_RDONLY | os.O_DIRECTORY)
            try:
                os.fsync(descriptor)
            finally:
                os.close(descriptor)
    except BaseException as exc:
        if installed:
            raise RuntimeError("The verified self-contained PDF was atomically installed, but a sidecar or directory-sync operation failed. Inspect the target before retrying; its previous bytes have already been replaced.") from exc
        raise
    finally:
        for path in staged:
            path.unlink(missing_ok=True)

    print(json.dumps({
        "status": "PASS", "output": str(TARGET),
        "record_sha256": verification["record_sha256"], "record_bytes": len(pdf_bytes),
        "pages": pages, "attachments": attachment_count,
        "predecessor_payload_files_preserved": EXPECTED_PREDECESSOR_FILES,
        "predecessor_manifest_preserved": True,
        "advance_files_included": len(advance_paths),
        "manifest": str(MASTER_MANIFEST), "verification": str(VERIFICATION),
        "ZIP_created_or_updated": False,
    }, indent=2))


if __name__ == "__main__":
    main()
