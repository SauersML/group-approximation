#!/usr/bin/env python3
"""sc_trace.py <old.py> <new.py> <root>      (lane systolic-counts; runs ON MSI)

Explain the discharged-set delta between two verifiers on one corpus.

MONOTONE: for every declaration both index, old conclusion heads ⊆ new heads and old needs
          ⊆ new needs.  A violation could discharge a name by dropping a requirement.
GAINED:   the new producers of the name whose requirements are all discharged, and how the
          new script sees them (a conclusion completed the way Lean does, an in-place
          construction, or an old producer whose requirements became discharged).
LOST:     the new producers of the name, the requirements not discharged, and the
          requirements the old script never counted for the same declaration.
ROOTS:    requirements counted only by the new script, discharged under neither, that block a
          producer of a lost name.
"""
import collections
import importlib.util
import sys
from pathlib import Path

SKIP = ("structure", "class", "inductive", "axiom", "opaque")


def load(path: str, name: str):
    sys.path.insert(0, str(Path(path).resolve().parent))
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def clip(text: str, width: int = 240) -> str:
    text = " ".join(text.split())
    return text if len(text) <= width else text[:width] + "…"


def index(module, corpus, new: bool):
    names = corpus.corpus_types | corpus.corpus_props
    rows = {}
    for declarations in corpus.declarations.values():
        for d in declarations.values():
            if d.keyword in SKIP or module.laundered_premises(d):
                continue
            if new:
                def res(head, d=d):
                    return corpus.resolve(head, d.namespace)
                inplace = {res(h) for h in module.in_place_heads(d)} & names
            else:
                res = corpus.resolve
                inplace = set()
            concl = {res(h) for h in module.produced_heads(d)} & names
            needs = {res(b.head) for b in d.build_premises if res(b.head) in names}
            rows[(str(d.path), d.line, d.short_name)] = (concl, inplace, needs, d)
    return rows


def producers_of(rows, head):
    return [(key, *row) for key, row in rows.items()
            if row[3].short_name != head and (head in row[0] or head in row[1])]


def main() -> int:
    old = load(sys.argv[1], "cnmu_trace_old")
    new = load(sys.argv[2], "cnmu_trace_new")
    root = Path(sys.argv[3])
    oc = old.build_corpus(root)
    nc = new.build_corpus(root)
    orows = index(old, oc, False)
    nrows = index(new, nc, True)

    gained = sorted(nc.discharged - oc.discharged)
    lost = sorted(oc.discharged - nc.discharged)
    hgained = sorted(nc.discharged_honestly - oc.discharged_honestly)
    hlost = sorted(oc.discharged_honestly - nc.discharged_honestly)
    print(f"GAINED {len(gained)} LOST {len(lost)} HONEST_GAINED {len(hgained)} "
          f"HONEST_LOST {len(hlost)} HONEST_DELTA_EQUALS_DELTA "
          f"{hgained == gained and hlost == lost}")

    violations = 0
    only_old = sorted(set(orows) - set(nrows))
    only_new = sorted(set(nrows) - set(orows))
    for key in set(orows) & set(nrows):
        ohead, _, oneeds, _ = orows[key]
        nhead, ninplace, nneeds, _ = nrows[key]
        if not ohead <= (nhead | ninplace) or not oneeds <= nneeds:
            violations += 1
            if violations <= 10:
                print(f"MONOTONE-VIOLATION {key} heads-dropped={sorted(ohead - nhead - ninplace)} "
                      f"needs-dropped={sorted(oneeds - nneeds)}")
    print(f"MONOTONE violations={violations} only_old_rows={len(only_old)} "
          f"only_new_rows={len(only_new)}")
    for key in (only_old + only_new)[:10]:
        print(f"  unmatched row {key}")

    kinds = collections.Counter()
    for head in gained:
        print(f"== GAINED {head}")
        shown = 0
        for key, concl, inplace, needs, d in producers_of(nrows, head):
            if not needs <= nc.discharged:
                continue
            orow = orows.get(key)
            if orow is None:
                how = "old-unindexed"
            elif head in orow[0]:
                how = "cascade" if not orow[2] <= oc.discharged else "ANOMALY-old-producer"
            elif head in concl:
                how = "conclusion-completion"
            else:
                how = "in-place"
            kinds[how] += 1
            if shown >= 6:
                continue
            shown += 1
            taint = "tainted" if d.short_name in nc.sorry_tainted else "honest"
            print(f"  {how:21s} {taint:7s} {d.full_name} {key[0]}:{d.line} "
                  f"needs={sorted(needs)}")
            if how == "cascade":
                print(f"      newly discharged needs={sorted(needs & set(gained))}")
            elif how == "conclusion-completion":
                print(f"      conclusion: {clip(old._strip_premises(d.statement))}")
            elif how == "in-place":
                for line in (d.value or "").splitlines():
                    if head in line:
                        print(f"      built: {clip(line)}")
                        break
    print(f"GAINED-PRODUCER-KINDS {dict(kinds)}")

    roots = collections.Counter()
    for head in lost:
        print(f"== LOST {head}")
        entries = producers_of(nrows, head)
        if not entries:
            print("  ANOMALY: no new producer at all")
        for number, (key, concl, inplace, needs, d) in enumerate(entries):
            orow = orows.get(key)
            missing = sorted(needs - nc.discharged)
            newly = needs - orow[2] if orow else set()
            for name in newly:
                if name not in oc.discharged and name not in nc.discharged:
                    roots[name] += 1
            if number < 8:
                print(f"  {d.full_name} {key[0]}:{d.line} missing={missing} "
                      f"newly-counted={sorted(newly) if orow else 'old-unindexed'}")
            if not missing:
                print("  ANOMALY: all requirements discharged")
        if len(entries) > 8:
            print(f"  … {len(entries) - 8} more producers")
    print("ROOTS " + ", ".join(f"{name}×{count}" for name, count in roots.most_common()))

    for name in ("normalizesNoNontrivialFinite_of_isHyperbolicallyEmbedded", "cutLiftOutcome",
                 "toCutMove", "CutLift.toCutMove"):
        for label, module, corpus in (("old", old, oc), ("new", new, nc)):
            declaration = corpus.by_name.get(name)
            if declaration is None:
                continue
            found = module.classify(corpus, declaration, set(), name)
            print(f"CLASSIFY {label} {name}: "
                  + ("; ".join(f"{kind}: {clip(detail, 160)}" for kind, detail in found)
                     or "clean"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
