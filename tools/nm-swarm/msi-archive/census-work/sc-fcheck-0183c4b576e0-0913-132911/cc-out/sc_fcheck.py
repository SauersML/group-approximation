#!/usr/bin/env python3
"""sc_fcheck.py <root>      (lane systolic-counts; runs ON MSI)

Check the hand-assembled flip list.  Each consumer and each least-area form is given as path:line on
main.  For every pair, print:
- the consumer's off-route needs and its other requirements missing under LA;
- whether the form is reachable from the root, sorry-tainted, or missing requirements under LA;
- what the flip would add to the consumer's requirements.
A composite target (a form applied to another) counts the union of needs minus the heads the parts produce.
"""
import collections
import importlib
import os
import re
import sys
from pathlib import Path

LA = "RelativeGreendlingerQuasiGeodesicLeastAreaStatement"
OFF = {"EstimatingUnboundOutputStatement", "EstimatingSelectionConstructionStatement",
       "RelativeGreendlingerQuasiGeodesicStatement", "RelativeGreendlingerStatement"}
OLD_BRIDGE = "RelativeIsoperimetricBridgeQuasiGeodesicStatement"
SKIP = ("structure", "class", "inductive", "axiom", "opaque")
IMPORT = re.compile(r"^import +([A-Za-z0-9_.']+)", re.M)
G = "GroupApproximation/GGT/"
M = "GroupApproximation/Manuscript/NonMF/"
TW = G + "HullSCLeastAreaGreendlingerTwins.lean"
BLC = G + "HullSCLemma44BoundedLeastAreaCanonical.lean"
LAA = M + "TorsionFreeLeastAreaAssembly.lean"
PHL = M + "TorsionFreeHullPrintedLeastArea.lean"
SSL = M + "TorsionFreeSectionSentencesLeastArea.lean"
TCA = M + "TheoremCAssembly.lean"
QGL = G + "HullSCOneStepQuasiGeodesicLeaves.lean"
PDC = G + "HullSCLemma49PowerDiagramFromComponents.lean"
TLA = M + "TorsionFreeLeafAssembly.lean"
TSS = M + "TorsionFreeSectionSentences.lean"

FLIPS = [
    (G + "HullSCLemma44CertificateInjectivity.lean", 143, [(TW, 311)]),
    (G + "HullSCLemma49Assemble.lean", 65, [(TW, 883)]),
    (G + "HullSCLemma49Assemble.lean", 160, [(TW, 883)]),
    (G + "HullSCLemma49Assemble.lean", 172, [(TW, 883)]),
    (G + "HullSCLemma49Assemble.lean", 193, [(TW, 883)]),
    (G + "HullSCLemma49FixedDelta.lean", 24, [(TW, 447)]),
    (G + "HullSCLemma49FixedDelta.lean", 81, [(TW, 547)]),
    (G + "HullSCLemma49InjectivityBridge.lean", 46, [(TW, 354)]),
    (G + "HullSCLemma49LongPeriod.lean", 94, [(TW, 447)]),
    (G + "HullSCLemma49LongPeriod.lean", 151, [(TW, 447)]),
    (PDC, 69, [(TW, 883)]),
    (PDC, 87, [(TW, 883)]),
    (PDC, 104, [(TW, 896)]),
    (PDC, 126, [(TW, 883)]),
    (PDC, 139, [(TW, 896)]),
    (PDC, 152, [(TW, 311)]),
    (G + "HullSCLemma49ShortLoxodromic.lean", 145, [(TW, 547)]),
    (G + "HullSCLemma49ShortLoxodromic.lean", 293, [(TW, 547)]),
    (G + "HullSCLemma49SourceAssembly.lean", 90, [(TW, 772)]),
    (G + "HullSCLemma49SourceBranches.lean", 53, [(TW, 447)]),
    (G + "HullSCLemma49SourceBranches.lean", 168, [(TW, 547)]),
    (QGL, 85, [(TW, 896)]),
    (QGL, 98, [(BLC, 140)]),
    (QGL, 115, [(G + "HullSC.lean", 625), (BLC, 140)]),
    (QGL, 126, [(TCA, 259)]),
    (G + "HullSCRelativeGreendlingerGeodesicConsumers.lean", 127, [(TW, 311)]),
    (G + "HullSCRelativeGreendlingerGeodesicConsumers.lean", 154, [(TW, 211)]),
    (G + "HullSCRelativeGreendlingerQuasiGeodesicSpelling.lean", 117, [(TW, 126)]),
    (G + "HullSCRelativeGreendlingerQuasiGeodesicSpelling.lean", 188, [(TW, 126)]),
    (G + "HullSCRelativeGreendlingerQuasiGeodesicSpelling.lean", 219, [(TW, 126)]),
    (G + "HullSCRelativeGreendlingerSpelling.lean", 335, [(TW, 211)]),
    (G + "HullSCRelativeGreendlingerSpelling.lean", 407, [(TW, 211)]),
    (G + "VanKampen/RelativeDiscRealizationPowerCertificate.lean", 100, [(TW, 47)]),
    (TLA, 93, [(TW, 126)]),
    (TLA, 113, [(TW, 896)]),
    (TLA, 126, [(BLC, 140)]),
    (TLA, 142, [(LAA, 38)]),
    (TLA, 152, [(LAA, 47)]),
    (TLA, 164, [(LAA, 57)]),
    (TLA, 173, [(LAA, 66)]),
    (TLA, 173, [(TCA, 333)]),
    (TLA, 262, [(LAA, 78)]),
    (M + "TorsionFreeSectionAssemblyClosedGO.lean", 61, [(M + "TorsionFreeSectionAssemblyClosedGO.lean", 74)]),
    (TSS, 71, [(PHL, 32)]),
    (TSS, 93, [(PHL, 58)]),
    (TSS, 126, [(PHL, 72)]),
    (TSS, 165, [(SSL, 37)]),
    (TSS, 188, [(SSL, 57)]),
    (TSS, 210, [(SSL, 75)]),
]
NEAREST = [(BLC, 44), (BLC, 123)]
FACTS = ("HullLemma44CanonicalQuotientStatement", OLD_BRIDGE,
         "RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement", LA)


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


def main():
    root = Path(sys.argv[1]).resolve()
    sys.path.insert(0, str(root / "scripts"))
    m = importlib.import_module("check_non_mf_unconditional")
    corpus = m.build_corpus(root)
    names = corpus.corpus_types | corpus.corpus_props
    tainted = corpus.sorry_tainted
    reach = reachable(root)

    def module_of(d):
        return os.path.relpath(d.path, root)[:-len(".lean")].replace("/", ".")

    at = {}
    producers = collections.defaultdict(list)
    for declarations in corpus.declarations.values():
        for d in declarations.values():
            if d.keyword in SKIP:
                continue
            res = lambda h, ns=d.namespace: corpus.resolve(h, ns)
            heads = ({res(h) for h in m.produced_heads(d) | m.in_place_heads(d)} & names) - {d.short_name}
            needs = {res(b.head) for b in d.build_premises if res(b.head) in names}
            at[(os.path.relpath(d.path, root), d.line)] = (d, heads, needs)
            if not m.laundered_premises(d):
                for h in heads:
                    producers[h].append(needs)

    def fixed_point(assume):
        out = set(assume)
        changed = True
        while changed:
            changed = False
            for head, entries in producers.items():
                if head not in out and any(needs <= out for needs in entries):
                    out.add(head)
                    changed = True
        return out

    D0 = fixed_point(())
    DLA = fixed_point({LA})
    print(f"SANITY discharged-match={D0 == corpus.discharged} D0={len(D0)} LA={len(DLA)} "
          f"modules-reachable={len(reach)}")
    for n in FACTS:
        print(f"FACT {n} in-D0={n in D0} in-LA={n in DLA} producers={len(producers.get(n, []))}")

    clean_count = 0
    for cpath, cline, targets in FLIPS:
        c = at.get((cpath, cline))
        parts = [at.get(t) for t in targets]
        if c is None or any(p is None for p in parts):
            print(f"MISSING {cpath}:{cline} -> {targets} consumer-found={c is not None}")
            continue
        cd, _, cneeds = c
        theads = set().union(*(p[1] | {p[0].short_name} for p in parts))
        tneeds = set().union(*(p[2] for p in parts)) - theads
        missing = sorted(tneeds - DLA)
        adds = sorted(tneeds - DLA - cneeds)
        treach = all(module_of(p[0]) in reach for p in parts)
        ttaint = [p[0].short_name for p in parts if p[0].short_name in tainted]
        clean = not missing and treach and not ttaint and not tneeds & OFF
        clean_count += clean
        print(f"{'CLEAN' if clean else 'CHECK'} {cd.short_name} {cpath}:{cline} off={sorted(cneeds & OFF)} "
              f"old-bridge={OLD_BRIDGE in cneeds} other-missing-under-LA={sorted(cneeds - DLA - OFF - {OLD_BRIDGE})}")
        shown = " + ".join(f"{p[0].full_name} {t[0]}:{t[1]}" for p, t in zip(parts, targets))
        print(f"      -> {shown} reach={treach} tainted={ttaint} missing-under-LA={missing} adds={adds}")
    print(f"FLIPS pairs={len(FLIPS)} clean={clean_count}")

    for key in NEAREST:
        p = at.get(key)
        if p is None:
            print(f"NEAREST MISSING {key}")
            continue
        print(f"NEAREST {p[0].full_name} {key[0]}:{key[1]} reach={module_of(p[0]) in reach} "
              f"tainted={p[0].short_name in tainted} missing-under-LA={sorted(p[2] - DLA)} heads={sorted(p[1])}")

    suffixes = ("_of_leaves", "_of_quasiGeodesicLeaves", "_of_leaves_closedCitations")
    for (path, line), (d, _, needs) in sorted(at.items()):
        if d.short_name.endswith(suffixes) and needs & OFF:
            print(f"LEAVES {d.short_name} {path}:{line} old-bridge={OLD_BRIDGE in needs}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
