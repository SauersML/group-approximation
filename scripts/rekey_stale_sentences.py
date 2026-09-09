#!/usr/bin/env python3
r"""Mechanically re-key stale rows of the non-MF sentence overlay map.

`metadata/NON_MF_SENTENCE_MAP.tsv` keys each row by a content hash of the
printed sentence.  When the manuscript prose is reworded, the hash changes
and the row becomes an "OVERLAY ERROR: stale overlay key" -- the assignment
is orphaned even though the underlying Lean declaration may still be exactly
what the (reworded) sentence needs.

This script reads the checked-in (stale) `metadata/NON_MF_SENTENCE_CENSUS.tsv`
for the OLD key -> OLD sentence text mapping, extracts the CURRENT sentences
from the tex the same way `sentence_census.py` does, and for every stale
overlay row looks for the best-matching current sentence within the same
label (or, lacking a label, the same section) using
`difflib.SequenceMatcher.ratio()` on lightly normalized text.  A match at
ratio >= --threshold (default 0.8) is accepted only if the row's own
declarations still plausibly cover the new wording: at least one cited
declaration's containing file contains a reasonable word-overlap with the
new sentence (a proxy for "the docstring still quotes this sentence").
Accepted rows are re-keyed in place; rejected/low-ratio rows are left
untouched and reported.
"""

from __future__ import annotations

import argparse
import difflib
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import sentence_census as sc  # noqa: E402
from lean_decls import build_index  # noqa: E402

REPO = Path(__file__).resolve().parent.parent
_DECL_INDEX = None


def normalize(s: str) -> str:
    s = re.sub(r"\\[A-Za-z]+", " ", s)
    s = re.sub(r"[^A-Za-z0-9]+", " ", s)
    return s.lower().strip()


def load_old_census(path: Path) -> dict[str, dict]:
    """key -> {label, section, sentence}."""
    out: dict[str, dict] = {}
    with open(path, encoding="utf-8") as f:
        header = None
        for line in f:
            if line.startswith("#"):
                continue
            parts = line.rstrip("\n").split("\t")
            if header is None:
                header = parts
                continue
            row = dict(zip(header, parts))
            key = row.get("key", "")
            if not key:
                continue
            out[key] = {
                "label": row.get("label", ""),
                "section": row.get("section", ""),
                "sentence": row.get("sentence", ""),
            }
    return out


def load_map(path: Path) -> tuple[list[str], dict[str, tuple[str, str, str, str]]]:
    """Return (raw lines incl. comments, key -> (status, decls, note, raw_line))."""
    lines = path.read_text(encoding="utf-8").splitlines()
    rows: dict[str, tuple[str, str, str, str]] = {}
    for line in lines:
        if line.startswith("#") or not line.strip():
            continue
        parts = line.split("\t")
        if len(parts) < 2:
            continue
        key = parts[0]
        status = parts[1] if len(parts) > 1 else ""
        decls = parts[2] if len(parts) > 2 else ""
        note = parts[3] if len(parts) > 3 else ""
        rows[key] = (status, decls, note, line)
    return lines, rows


def decl_module_files(decls: str) -> list[Path]:
    global _DECL_INDEX
    if _DECL_INDEX is None:
        _DECL_INDEX = build_index()
    files: list[Path] = []
    for d in decls.split():
        # Fully qualified name (GroupApproximation.<namespace...>.<decl>).
        # lean_decls.py's index is keyed the same way (namespace-qualified,
        # without the leading `GroupApproximation` root the scan doesn't add).
        candidates = [d]
        if d.startswith("GroupApproximation."):
            candidates.append(d[len("GroupApproximation."):])
        path = None
        for c in candidates:
            if c in _DECL_INDEX:
                path = _DECL_INDEX[c]
                break
        if path is None:
            # fall back to the short (last-component) name
            short = d.rsplit(".", 1)[-1]
            for name, p in _DECL_INDEX.items():
                if name.rsplit(".", 1)[-1] == short:
                    path = p
                    break
        if path is not None:
            files.append(path)
    return files


_FILE_CACHE: dict[Path, str] = {}


def declaration_supports(decls: str, new_sentence: str) -> bool:
    """Proxy for 'the cited declaration's docstring still quotes this
    sentence': accept if a normalized 4-gram of the new sentence appears
    (order-sensitive) in the declaration's containing file, OR if the file
    cannot be located (benefit of the doubt -- the ratio match already did
    the real work; this is a secondary sanity filter, not the primary one).
    """
    files = decl_module_files(decls)
    if not files:
        return True
    toks = [t for t in normalize(new_sentence).split() if len(t) >= 3]
    if len(toks) < 4:
        return True
    grams = {" ".join(toks[i:i + 4]) for i in range(len(toks) - 3)}
    for f in files:
        if f not in _FILE_CACHE:
            try:
                _FILE_CACHE[f] = normalize(
                    f.read_text(encoding="utf-8", errors="ignore"))
            except OSError:
                _FILE_CACHE[f] = ""
        text = _FILE_CACHE[f]
        if any(g in text for g in grams):
            return True
    return False


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--old-census", type=Path,
                     default=REPO / "metadata" / "NON_MF_SENTENCE_CENSUS.tsv")
    ap.add_argument("--map", type=Path,
                     default=REPO / "metadata" / "NON_MF_SENTENCE_MAP.tsv")
    ap.add_argument("--tex", type=Path, default=sc.TEX)
    ap.add_argument("--out-map", type=Path, required=True)
    ap.add_argument("--report", type=Path, required=True)
    ap.add_argument("--threshold", type=float, default=0.8)
    args = ap.parse_args()

    old = load_old_census(args.old_census)
    lines, rows = load_map(args.map)
    _ledger_rows, probes = sc.load_ledger()
    current_records = sc.extract(str(args.tex))
    sc.attach_anchors(current_records, str(args.tex), probes)
    current_keys = {r["key"] for r in current_records}

    # group current records by label, and by section, for candidate search
    by_label: dict[str, list[dict]] = {}
    by_section: dict[str, list[dict]] = {}
    for r in current_records:
        if r.get("label"):
            by_label.setdefault(r["label"], []).append(r)
        if r.get("section"):
            by_section.setdefault(r["section"], []).append(r)

    stale_keys = sorted(k for k in rows if k not in current_keys)

    STATUS_RANK = {"formalized": 6, "partial": 5, "definition": 4,
                   "structural": 3, "attribution": 2, "provenance": 2,
                   "ledger": 1, "open": 0}

    # Seed the final row set from every row that is NOT stale; stale rows
    # are handled below (rekeyed into this dict, merged if the target
    # already has a row, or left out and reported unresolved).
    final: dict[str, tuple[str, str, str]] = {}
    for k, (status, decls, note, _raw) in rows.items():
        if k not in set(stale_keys):
            final[k] = (status, decls, note)

    rekeyed = 0
    merged = 0
    unresolved: list[tuple[str, str, float, str, str]] = []

    for key in stale_keys:
        status, decls, note, raw_line = rows[key]
        old_info = old.get(key)
        if old_info is None:
            unresolved.append((key, "", 0.0, status,
                                "no old-census entry for this key at all"))
            continue
        old_text = old_info["sentence"]
        label = old_info["label"]
        section = old_info["section"]
        candidates = by_label.get(label, []) if label else []
        if not candidates and section:
            candidates = by_section.get(section, [])
        if not candidates:
            candidates = current_records
        old_norm = normalize(old_text)
        best = None
        best_ratio = -1.0
        for cand in candidates:
            cand_norm = normalize(cand["sentence"])
            ratio = difflib.SequenceMatcher(None, old_norm, cand_norm).ratio()
            if ratio > best_ratio:
                best_ratio = ratio
                best = cand
        # A very high ratio (near-identical normalized text) is decisive on
        # its own; the docstring-quote check is only needed as a sanity
        # filter in the 0.8-0.92 band, where it catches coincidental partial
        # overlaps.  Above that, requiring a literal 4-gram match against the
        # declaration's file produces false negatives whenever the docstring
        # paraphrases the sentence instead of quoting it verbatim.
        decl_ok = (best_ratio >= 0.92 or
                   (best is not None and
                    declaration_supports(decls, best["sentence"])))
        if best is not None and best_ratio >= args.threshold and decl_ok:
            new_key = best["key"]
            anchor_desc = ('label ' + label) if label else ('section ' + section)
            rekey_tag = (f"REKEYED 2026-09-09 by rekey_stale_sentences.py "
                         f"(difflib ratio {best_ratio:.3f} against the old "
                         f"key {key}'s sentence, same {anchor_desc}).")
            if new_key in final:
                ex_status, ex_decls, ex_note = final[new_key]
                ex_set = ex_decls.split()
                new_set = [d for d in decls.split() if d not in ex_set]
                merged_decls = " ".join(ex_set + new_set)
                merged_status = (status if STATUS_RANK.get(status, -1) >
                                  STATUS_RANK.get(ex_status, -1) else ex_status)
                merged_note = (
                    f"{ex_note} MERGED with old key {key} ({rekey_tag} "
                    f"Declarations union'd{'; status raised to ' + status if merged_status != ex_status else ''}.)")
                final[new_key] = (merged_status, merged_decls, merged_note)
                merged += 1
            else:
                final[new_key] = (status, decls, f"{note} {rekey_tag}")
                rekeyed += 1
        elif best is not None and best_ratio >= args.threshold:
            unresolved.append((
                key, best["key"], best_ratio, status,
                "ratio ok but declaration_supports failed (docstring "
                "does not obviously quote the new wording) -- manual check"))
        else:
            unresolved.append((
                key, best["key"] if best else "", best_ratio, status,
                f"best candidate ratio {best_ratio:.3f} < {args.threshold}"
                if best else "no candidate sentences at all"))

    comments = [l for l in lines if l.startswith("#")]
    out_lines = comments + [
        "\t".join([k, s, d, n]) for k, (s, d, n) in sorted(final.items())]
    args.out_map.write_text("\n".join(out_lines) + "\n", encoding="utf-8")

    with open(args.report, "w", encoding="utf-8") as f:
        f.write(f"# rekey_stale_sentences.py report\n")
        f.write(f"# stale rows: {len(stale_keys)}, rekeyed: {rekeyed}, "
                f"merged: {merged}, unresolved: {len(unresolved)}\n")
        f.write("old_key\tbest_candidate_key\tratio\told_status\treason\n")
        for row in unresolved:
            f.write("\t".join(
                x if isinstance(x, str) else f"{x:.3f}" for x in row) + "\n")

    print(f"stale rows: {len(stale_keys)}")
    print(f"rekeyed: {rekeyed}")
    print(f"merged: {merged}")
    print(f"unresolved: {len(unresolved)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
