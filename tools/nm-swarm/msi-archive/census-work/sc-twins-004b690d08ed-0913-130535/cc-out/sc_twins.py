#!/usr/bin/env python3
"""sc_twins.py <root>      (lane systolic-counts; runs ON MSI)

Per-consumer flip list for the Props off the ruled route.  The ruled route proves only
RelativeGreendlingerQuasiGeodesicLeastAreaStatement (LA).  For every declaration that needs one of
the four off-route Props, report the least-area forms that replace it and whether anything uses it.

STATUS:   producers and refutations of each off-route Prop, with requirements missing under LA.
CONSUMER: off-route needs (written spelling), other requirements missing under LA, heads and which
          heads LA discharges, root reachability, users, census rows, docstring marks.
TWINS:    name twins (same stem spelled leastArea), head twins (other producers of a head needing
          no off-route Prop), spelled twins (the head's name with LeastArea or Embedded added).
VERDICT:  BRIDGE | FLIP (clean name twin) | LA-SPELLED (a least-area spelled head discharged) |
          COVERED (every head discharged under LA, head level only) | SUPERSEDED (no least-area form).
OFFONLY:  names discharged with every off-route Prop assumed but not under LA alone.
"""
import collections
import importlib
import os
import re
import sys
from pathlib import Path

LA = "RelativeGreendlingerQuasiGeodesicLeastAreaStatement"
OFF = ("EstimatingUnboundOutputStatement", "EstimatingSelectionConstructionStatement",
       "RelativeGreendlingerQuasiGeodesicStatement", "RelativeGreendlingerStatement")
BRIDGE = "relativeGreendlingerQuasiGeodesicLeastArea_of_reduced"
SKIP = ("structure", "class", "inductive", "axiom", "opaque")
COUNTED = {"formalized", "definition", "partial"}
MARKS = ("supersed", "historical", "legacy", "ruled route", "still open", "refuted", "vacuous")
TOKEN = re.compile(r"[A-Za-z0-9_'.]+")
IMPORT = re.compile(r"^import +([A-Za-z0-9_.']+)", re.M)


def clip(text, width=200):
    text = " ".join(str(text).split())
    return text if len(text) <= width else text[:width] + "…"


def stem(name):
    return name.replace("LeastArea", "").replace("leastArea", "").split("_of_")[0]


def spelled(name):
    return name.replace("LeastArea", "").replace("Embedded", "")


def reachable(root):
    seen, todo = set(), ["GroupApproximation"]
    while todo:
        module = todo.pop()
        if module in seen:
            continue
        seen.add(module)
        try:
            text = (root / (module.replace(".", "/") + ".lean")).read_text(errors="replace")
        except OSError:
            continue
        todo.extend(IMPORT.findall(text))
    return seen


def docstring(d, cache):
    lines = cache.get(str(d.path))
    if lines is None:
        lines = cache[str(d.path)] = Path(d.path).read_text(errors="replace").splitlines()
    i = d.line - 2
    while i >= 0 and lines[i].lstrip().startswith("@["):
        i -= 1
    if i < 0 or not lines[i].rstrip().endswith("-/"):
        return ""
    j = i
    while j > max(i - 80, 0) and "/--" not in lines[j]:
        j -= 1
    return " ".join(lines[j:i + 1])


def main():
    root = Path(sys.argv[1]).resolve()
    sys.path.insert(0, str(root / "scripts"))
    m = importlib.import_module("check_non_mf_unconditional")
    sc = importlib.import_module("sentence_census")
    corpus = m.build_corpus(root)
    names = corpus.corpus_types | corpus.corpus_props
    tainted = corpus.sorry_tainted
    reach = reachable(root)
    cache = {}

    def rel(d):
        return f"{os.path.relpath(d.path, root)}:{d.line}"

    def module_of(d):
        return os.path.relpath(d.path, root)[:-len(".lean")].replace("/", ".")

    rows = []  # (declaration, heads, needs -> written type text, laundered)
    for declarations in corpus.declarations.values():
        for d in declarations.values():
            if d.keyword in SKIP:
                continue
            res = lambda h, ns=d.namespace: corpus.resolve(h, ns)
            heads = {res(h) for h in m.produced_heads(d) | m.in_place_heads(d)} & names
            needs = {}
            for b in d.build_premises:
                if res(b.head) in names:
                    needs.setdefault(res(b.head), b.type_text)
            rows.append((d, heads - {d.short_name}, needs, bool(m.laundered_premises(d))))
    producers = collections.defaultdict(list)
    for d, heads, needs, laundered in rows:
        if not laundered:
            for h in heads:
                producers[h].append((d, set(needs)))
    by_stem = collections.defaultdict(list)
    for row in rows:
        by_stem[stem(row[0].short_name)].append(row)
    by_spelled = collections.defaultdict(list)
    for n in names:
        if "LeastArea" in n or "Embedded" in n:
            by_spelled[spelled(n)].append(n)

    def fixed_point(assume):
        out = set(assume)
        changed = True
        while changed:
            changed = False
            for head, entries in producers.items():
                if head not in out and any(needs <= out for _, needs in entries):
                    out.add(head)
                    changed = True
        return out

    D0 = fixed_point(())
    DLA = fixed_point({LA})
    DALL = fixed_point({LA, *OFF})
    print(f"SANITY discharged-match={D0 == corpus.discharged} names={len(names)} rows={len(rows)} "
          f"D0={len(D0)} LA={len(DLA)} ALL={len(DALL)} modules-reachable={len(reach)} "
          f"embedded-bridge-in-D0={'RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement' in D0}")

    records = sc.extract(sc.TEX)
    ledger_rows, probes = sc.load_ledger(sc.LEDGER)
    sc.attach_anchors(records, sc.TEX, probes)
    records = sc.join(records, sc.load_map(sc.MAP), ledger_rows, True)
    cited = collections.defaultdict(list)
    for r in records:
        if r["status"] in COUNTED:
            for name in r["decls"].split():
                cited[name].append(f"{r['key']}({r['status']})")

    for r in OFF:
        print(f"\n== STATUS {r} D0={r in D0} LA={r in DLA}")
        for d, needs in producers.get(r, []):
            print(f"  producer {d.full_name} {rel(d)} missing-under-LA={sorted(needs - DLA)}"
                  f"{' TAINTED' if d.short_name in tainted else ''}")
        pat = re.compile(rf"(^|[^A-Za-z0-9_]){r}([^A-Za-z0-9_]|$)")
        for d, *_ in rows:
            concl = m._strip_premises(d.statement)
            if m.is_refutation(concl) and pat.search(concl):
                print(f"  refutation {d.full_name} {rel(d)}: {clip(concl, 160)}")

    consumers = {}
    for row in rows:
        blockers = [r for r in OFF if r in row[2]]
        if blockers:
            consumers[row[0].full_name] = (row, blockers)
    targets = {row[0].short_name for row, _ in consumers.values()}
    users = collections.defaultdict(set)
    for d, *_ in rows:
        for token in TOKEN.findall(d.value or ""):
            last = token.rsplit(".", 1)[-1]
            if last in targets and last != d.short_name:
                users[last].add(d.full_name)

    def clean(t, tneeds):
        tneeds = set(tneeds)
        return not tneeds & set(OFF) and tneeds <= DLA and t.short_name not in tainted

    by_file = collections.defaultdict(list)
    for row, blockers in consumers.values():
        by_file[os.path.relpath(row[0].path, root)].append((row, blockers))
    counts = collections.Counter()
    print(f"\nCONSUMERS unique={len(consumers)} files={len(by_file)}")
    for path in sorted(by_file):
        print(f"\n== FILE {path} root-reachable={path[:-5].replace('/', '.') in reach}")
        for (d, heads, needs, laundered), blockers in sorted(by_file[path], key=lambda x: x[0][0].line):
            name_twins = []
            for t, theads, tneeds, tlaundered in by_stem.get(stem(d.short_name), []):
                if t is d or "eastArea" not in t.short_name or tlaundered:
                    continue
                name_twins.append((clean(t, tneeds), t, sorted(set(tneeds) - DLA)))
            spelled_la = sorted({n for h in heads - DLA for n in by_spelled.get(spelled(h), ())
                                 if n != h and n in DLA})
            clean_names = [t for ok, t, _ in name_twins if ok]
            if d.short_name == BRIDGE:
                verdict = "BRIDGE"
            elif clean_names:
                verdict = "FLIP " + clean_names[0].full_name
            elif spelled_la:
                verdict = "LA-SPELLED " + ",".join(spelled_la)
            elif heads and heads <= DLA:
                verdict = "COVERED"
            else:
                verdict = "SUPERSEDED"
            counts[verdict.split()[0]] += 1
            doc = docstring(d, cache).lower()
            marks = [w for w in MARKS if w in doc]
            use = sorted(users.get(d.short_name, ()))
            print(f"  {d.short_name} :{d.line} kw={d.keyword}"
                  f"{' TAINTED' if d.short_name in tainted else ''}"
                  f"{' LAUNDERED' if laundered else ''} VERDICT={verdict}")
            print("      needs-off " + "; ".join(f"{r}={clip(needs[r], 80)}" for r in blockers))
            print(f"      other-missing-under-LA={sorted(set(needs) - DLA - set(OFF))} "
                  f"heads={sorted(heads)} under-LA={sorted(heads & DLA)}")
            print(f"      users={len(use)} {[u.rsplit('.', 1)[-1] for u in use[:6]]} "
                  f"census={cited.get(d.full_name, [])} doc-marks={marks}")
            for ok, t, miss in name_twins[:4]:
                print(f"      name-twin {'CLEAN' if ok else 'missing=' + str(miss)} {t.full_name} "
                      f"{rel(t)} reach={module_of(t) in reach} census={cited.get(t.full_name, [])}")
            for h in sorted(heads):
                entries = [(clean(t, tn), t, sorted(tn - DLA)) for t, tn in producers.get(h, [])
                           if t is not d and not tn & set(OFF)]
                good = [e for e in entries if e[0]]
                for ok, t, miss in (good[:2] or entries[:1]):
                    print(f"      head-twin {h} {'CLEAN' if ok else 'missing=' + str(miss)} "
                          f"{t.full_name} {rel(t)} (clean {len(good)}/{len(entries)})")
            for h in sorted(heads - DLA):
                for n in by_spelled.get(spelled(h), ()):
                    if n == h:
                        continue
                    prod = [t for t, tn in producers.get(n, []) if clean(t, tn)]
                    print(f"      spelled-twin {h} -> {n} in-LA={n in DLA} "
                          f"producer={prod[0].full_name + ' ' + rel(prod[0]) if prod else None}")
    print(f"\nVERDICTS {dict(counts)}")

    print(f"\nOFFONLY {len(DALL - DLA)}")
    for n in sorted(DALL - DLA):
        decl = corpus.by_name.get(n)
        full = decl.full_name if decl is not None else n
        print(f"  {n} census={cited.get(full, [])} producers={len(producers.get(n, []))} "
              f"spelled={[s for s in by_spelled.get(spelled(n), ()) if s != n and s in DLA]}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
