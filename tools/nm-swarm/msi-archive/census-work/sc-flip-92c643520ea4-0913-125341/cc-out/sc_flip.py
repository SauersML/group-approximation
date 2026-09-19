#!/usr/bin/env python3
"""sc_flip.py <root>      (lane systolic-counts; runs ON MSI)

Flip list for the consumers blocked by Props off the ruled route.  The ruled route proves only
RelativeGreendlingerQuasiGeodesicLeastAreaStatement (LA).  Assume LA discharged, then each
off-route Prop singly and all of them, rerunning the verifier's own fixed point.

BLOCKER:  producers (missing requirements under LA) and refutations of each off-route Prop.
CONSUMER: every producer row needing an off-route Prop: written spelling, other requirements
          missing under LA, taint, census rows citing it.
FLIP:     census findings that survive LA and clear once off-route Props are assumed, with the
          single Props that clear each, the witness chain down to the Prop, and least-area twins
          (same conclusion head clean under LA, or the same name stem spelled leastArea).
REST:     census findings that survive even with every off-route Prop assumed, by detector.
"""
import collections
import dataclasses
import importlib
import os
import re
import sys
from pathlib import Path

LA = "RelativeGreendlingerQuasiGeodesicLeastAreaStatement"
OFF = ("EstimatingUnboundOutputStatement", "EstimatingSelectionConstructionStatement",
       "RelativeGreendlingerQuasiGeodesicStatement", "RelativeGreendlingerStatement")
SKIP = ("structure", "class", "inductive", "axiom", "opaque")
COUNTED = {"formalized", "definition", "partial"}


def clip(text, width=240):
    text = " ".join(str(text).split())
    return text if len(text) <= width else text[:width] + "…"


def stem(name):
    return name.replace("LeastArea", "").replace("leastArea", "").split("_of_")[0]


def main():
    root = Path(sys.argv[1]).resolve()
    sys.path.insert(0, str(root / "scripts"))
    m = importlib.import_module("check_non_mf_unconditional")
    sc = importlib.import_module("sentence_census")
    corpus = m.build_corpus(root)
    names = corpus.corpus_types | corpus.corpus_props
    tainted = corpus.sorry_tainted

    def rel(d):
        return f"{os.path.relpath(d.path, root)}:{d.line}"

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
    by_full = collections.defaultdict(list)
    by_stem = collections.defaultdict(list)
    for row in rows:
        by_full[row[0].full_name].append(row)
        by_stem[stem(row[0].short_name)].append(row)

    def fixed_point(assume, honest):
        out, why = set(assume), {}
        changed = True
        while changed:
            changed = False
            for head, entries in producers.items():
                if head in out:
                    continue
                for d, needs in entries:
                    if honest and d.short_name in tainted:
                        continue
                    if needs <= out:
                        out.add(head)
                        why[head] = (d, needs)
                        changed = True
                        break
        return out, why

    D0, _ = fixed_point((), False)
    H0, _ = fixed_point((), True)
    print(f"SANITY discharged-match={D0 == corpus.discharged} "
          f"honest-match={H0 == corpus.discharged_honestly} names={len(names)} rows={len(rows)}")
    assumptions = {"LA": {LA}, **{r: {LA, r} for r in OFF}, "ALL": {LA, *OFF}}
    D = {k: fixed_point(v, False) for k, v in assumptions.items()}
    H = {k: fixed_point(v, True)[0] for k, v in assumptions.items()}
    DLA, DALL, WHY = D["LA"][0], D["ALL"][0], D["ALL"][1]
    print(f"SIZES D0={len(D0)} " + " ".join(f"{k}={len(D[k][0])}" for k in D))
    print(f"LA in D0={LA in D0} honest={LA in H0}")

    records = sc.extract(sc.TEX)
    ledger_rows, probes = sc.load_ledger(sc.LEDGER)
    sc.attach_anchors(records, sc.TEX, probes)
    records = sc.join(records, sc.load_map(sc.MAP), ledger_rows, True)
    cited = collections.defaultdict(list)
    for r in records:
        if r["status"] in COUNTED:
            for name in r["decls"].split():
                cited[name].append(f"{r['key']}({r['status']})")

    def chain(name, depth=1, seen=None):
        seen = set() if seen is None else seen
        pad = "    " * depth
        if name in seen or depth > 12:
            return [f"{pad}<- {name} (seen)"]
        seen.add(name)
        if name in OFF:
            return [f"{pad}<- {name} [OFF-ROUTE]"]
        if name not in WHY:
            return [f"{pad}<- {name} [undischarged even with every off-route Prop]"]
        d, needs = WHY[name]
        out = [f"{pad}<- {name} by {d.full_name} {rel(d)}"]
        for n in sorted(needs - DLA):
            out += chain(n, depth + 1, seen)
        return out

    def twins(d, heads, needs):
        out = []
        for h in sorted(heads):
            for t, tneeds in producers.get(h, []):
                if t is d or tneeds & set(OFF):
                    continue
                miss = sorted(tneeds - DLA)
                out.append(f"      head-twin {h}: {t.full_name} {rel(t)} "
                           f"{'CLEAN-UNDER-LA' if not miss else 'missing=' + str(miss)}"
                           f"{' TAINTED' if t.short_name in tainted else ''}")
        for t, theads, tneeds, laundered in by_stem.get(stem(d.short_name), []):
            if t is d or "eastArea" not in t.short_name:
                continue
            miss = sorted(set(tneeds) - DLA)
            out.append(f"      name-twin {t.full_name} {rel(t)} needs={sorted(tneeds)} "
                       f"{'CLEAN-UNDER-LA' if not miss else 'missing=' + str(miss)}"
                       f"{' LAUNDERED' if laundered else ''}"
                       f"{' TAINTED' if t.short_name in tainted else ''}")
        return out[:12]

    for r in OFF:
        print(f"\n== BLOCKER {r} D0={r in D0} LA={r in DLA}")
        for d, needs in producers.get(r, []):
            print(f"  producer {d.full_name} {rel(d)} missing-under-LA={sorted(needs - DLA)}"
                  f"{' TAINTED' if d.short_name in tainted else ''}")
        pat = re.compile(rf"(^|[^A-Za-z0-9_]){r}([^A-Za-z0-9_]|$)")
        for d, *_ in rows:
            concl = m._strip_premises(d.statement)
            if m.is_refutation(concl) and pat.search(concl):
                print(f"  refutation {d.full_name} {rel(d)}: {clip(concl, 160)}")
        consumers = [row for row in rows if r in row[2]]
        print(f"  consumers={len(consumers)}")
        for d, heads, needs, laundered in sorted(consumers, key=lambda x: rel(x[0])):
            print(f"  CONSUMER {d.full_name} {rel(d)} kw={d.keyword}"
                  f"{' TAINTED' if d.short_name in tainted else ''}{' LAUNDERED' if laundered else ''}")
            print(f"      written={clip(needs[r], 120)} heads={sorted(heads)}")
            print(f"      other-missing-under-LA={sorted(set(needs) - DLA - {r})} "
                  f"heads-under-LA={[h for h in sorted(heads) if h in DLA]} "
                  f"census={cited.get(d.full_name, [])}")

    from lean_decls import build_index
    paths = build_index(root)
    roster, _ = m.read_roster(root / m.DEFAULT_ROSTER)
    qualified = {}

    def findings(patched):
        out = {}
        for r in records:
            if r["status"] not in COUNTED:
                continue
            for name in r["decls"].split():
                path = paths.get(name)
                if path is not None and path not in qualified:
                    qualified[path] = m.scan_module(path, qualified=True)
                decl = qualified.get(path, {}).get(name)
                if decl is None:
                    continue
                for detector, detail in m.classify(patched, decl, roster, name):
                    if sc.counts_finding(r["status"], detector):
                        out[(r["key"], name, detector)] = detail
        return out

    official = {(k, n, det) for k, n, det, _ in sc.verify_unconditional(records)}
    F0 = findings(corpus)
    print(f"\nCROSSCHECK official={len(official)} mine={len(F0)} equal={official == set(F0)}")
    F = {k: findings(dataclasses.replace(corpus, discharged=D[k][0], discharged_honestly=H[k]))
         for k in assumptions}
    print("FINDINGS base=%d " % len(F0) + " ".join(f"{k}={len(F[k])}" for k in F))
    blocked = sorted(set(F["LA"]) - set(F["ALL"]))
    print(f"CLEARED-BY-LA={len(set(F0) - set(F['LA']))} BLOCKED-OFF-ROUTE={len(blocked)} "
          f"carriers={len({b[1] for b in blocked})}")
    grouped = collections.defaultdict(list)
    for key in blocked:
        grouped[key[1]].append(key)
    for name in sorted(grouped):
        singles = sorted({r for key in grouped[name] for r in OFF if key not in F[r]})
        print(f"\n== FLIP {name} singles={singles or 'JOINT-ONLY'}")
        for key in grouped[name]:
            print(f"    finding {key[0]} {key[2]}: {clip(F['LA'][key], 300)}")
        for d, heads, needs, laundered in by_full.get(name, []):
            print(f"    at {rel(d)} kw={d.keyword}{' TAINTED' if d.short_name in tainted else ''}"
                  f"{' LAUNDERED' if laundered else ''} heads={sorted(heads)}")
            for n in sorted(set(needs) - DLA):
                print("\n".join(chain(n)))
            print("\n".join(twins(d, heads, needs)))
    rest = collections.Counter(key[2] for key in F["ALL"])
    print(f"\nREST {dict(rest)}")
    for key in sorted(F["ALL"])[:40]:
        print(f"  rest {key[0]} {key[1]} {key[2]}: {clip(F['ALL'][key], 160)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
