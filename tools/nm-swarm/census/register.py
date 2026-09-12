#!/usr/bin/env python3
"""register.py <verify-unconditional.txt> <baseline in> <baseline out> <sha9>

Runs ON MSI (census merge).  Keeps metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt in step with
`sentence_census.py --verify-unconditional`:
  * a register line that matches no finding (STALE BASELINE) is commented out with the date and reason;
  * a NEW finding gets one justified line, classified by what its premise waits on, naming the rows that
    cite it and their owner lanes.  A finding the rules below cannot classify is NOT registered: it is
    printed as UNCLASSIFIED and the script exits 3, so the gate stays red until a person writes the line.
Exit 0 when every new finding was registered.
"""
import re
import sys

ver_path, base_in, base_out, sha9 = sys.argv[1:5]
lines = open(base_in, encoding="utf-8").read().split("\n")
if lines and lines[-1] == "":
    lines.pop()

stale, new = set(), {}
for raw in open(ver_path, encoding="utf-8"):
    p = raw.rstrip("\n").split("\t")
    if p[0] == "STALE BASELINE" and len(p) >= 3:
        stale.add((p[1], p[2]))
    elif p[0] == "CONDITIONAL" and len(p) >= 5:
        pair = (p[3], p[2])
        rec = new.setdefault(pair, {"rows": [], "detail": ""})
        if p[1] not in rec["rows"]:
            rec["rows"].append(p[1])
        rec["detail"] += " " + p[4]

registered = set()
out = []
entry = re.compile(r"^(?P<det>[a-z-]+)\s+(?P<decl>\S+)\s+--")
for line in lines:
    m = entry.match(line)
    if m and (m.group("det"), m.group("decl")) in stale:
        out.append("# REMOVED by the census merge at %s (stale: matches no finding): %s %s"
                   % (sha9, m.group("det"), m.group("decl")))
        continue
    if m:
        registered.add((m.group("det"), m.group("decl")))
    out.append(line)

RULES = [
    (lambda d, det, dt: "FullDefectCornerRemark.manuscriptSentence_cornerPassesUp" in d,
     "the premise FullDefectPair (Corner R p hp) is the printed hypothesis of the sentence itself (\"if the ring pRp, "
     "with unit p, satisfies the hypothesis\"), carried exactly as printed; not a citation"),
    (lambda d, det, dt: "powersAveragingEstimate_of_naiveFreeProductProperty" in d,
     "an intermediate lemma cited beside the closed endpoint dgoTheorem235Printed; NaiveFreeProductProperty G is the "
     "group property NaiveFreeProductAtAcylindricallyHyperbolicProof establishes at acylindrically hyperbolic groups; "
     "owners dgo-analytic, dgo-geometric, go-sr1"),
    (lambda d, det, dt: "KotowskiOllivierStatement" in dt,
     "Fournier-Facio's G_0 is fed by TheoremC.KotowskiOllivierStatement (a torsion-free hyperbolic property-(T) group), "
     "not yet produced; owners kh-hyperbolic, kh-torsion"),
    (lambda d, det, dt: "FinitelyPresentedInfiniteSimpleStatement" in dt,
     "FFF S2 needs a finitely presented torsion-free infinite simple group (FinitelyPresentedInfiniteSimpleStatement, "
     "Hyde-Lodha), not yet produced; owner simple-group"),
    (lambda d, det, dt: re.search(r"FournierFacioParagraph|LiteratureInputs", dt) or d.endswith("FournierFacioParagraph"),
     "the Fournier-Facio paragraph (FFF S2) is produced only through TheoremCAssembly's open admissions until "
     "KotowskiOllivierStatement and FinitelyPresentedInfiniteSimpleStatement are proved; owners simple-group, "
     "kh-hyperbolic, kh-torsion"),
    (lambda d, det, dt: re.search(r"EstimatingUnboundOutputStatement|RelativeIsoperimetricBridgeQuasiGeodesicStatement\."
                                  r"|RelativeGreendlingerQuasiGeodesicStatement\.", dt),
     "the historical quasi-geodesic leaves of Hull Theorem 7.1 (EstimatingUnboundOutputStatement is refuted on main, and "
     "no producer exists for the old bridge), cited beside the least-area route that replaces them; owners hull-select, "
     "hull-unbound, hull-bridge, hull-respell, sec5-sentences"),
    (lambda d, det, dt: re.search(r"RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement"
                                  r"|RelativeGreendlingerQuasiGeodesicLeastAreaStatement|QuotientPeripheralLetterPullback", dt),
     "over the least-area leaves of Hull Theorem 7.1 (RelativeGreendlingerQuasiGeodesicLeastAreaStatement, "
     "RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement and its letter pullback), not yet produced; owners "
     "hull-select, hull-unbound, hull-bridge, sec5-sentences"),
    (lambda d, det, dt: re.search(r"BoundedImageEmbeddingStatement|BoundedHullLemma44CanonicalQuotientStatement"
                                  r"|HullLemma44CanonicalQuotientStatement|HullOneStepStatementGeneral|HullTower", dt),
     "Hull's Lemma 4.4 and one-step quotient statements, produced only from the open Theorem 7.1 leaves; owners "
     "hull-respell, hull-bridge, sec5-sentences"),
    (lambda d, det, dt: det.startswith("carrier-") and re.search(r"TorsionFree|HullSmallCancellation|RegularNonMFAlgebra"
                                                                 r"|Saturation", d),
     "the printed statement named as vocabulary beside the leaf-conditional producers the rows cite; it is produced "
     "only through the open Hull 7.1 and FFF S2 leaves; owners sec5-sentences, hull-*, simple-group, kh-*"),
]

added, unclassified = [], []
for (det, decl), rec in new.items():
    if (det, decl) in registered:
        continue
    why = next((w for test, w in RULES if test(decl, det, rec["detail"])), None)
    if why is None:
        unclassified.append("%s %s rows %s: %s" % (det, decl, " ".join(rec["rows"]), rec["detail"][:300]))
        continue
    added.append("%s %s  -- rows %s (census merge %s): %s" % (det, decl, " ".join(rec["rows"]), sha9, why))

if added:
    out.append("#")
    out.append("# Added by the census merge at %s (lane go-lemma42, lead session nonsofic-existence-41): every line sits "
               "on a row graded partial, except a printed hypothesis where the line says so; a line goes the day its "
               "premise gets a closed producer or its row stops naming the declaration." % sha9)
    out.extend(added)
with open(base_out, "w", encoding="utf-8") as fh:
    fh.write("\n".join(out) + "\n")
print("register", sha9, "stale removed", len(stale), "new registered", len(added), "unclassified", len(unclassified))
for u in unclassified:
    print("UNCLASSIFIED", u)
sys.exit(3 if unclassified else 0)
