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

# The walls of sec:torsion-free as they stand on origin (09-13, after f65f99f17, 18682110d, 1edf0f7b4).
KO_PRODUCED = ("hKO: TheoremC.KotowskiOllivierStatement is closed by KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed "
               "(#audit_closed_axioms, root-imported, f65f99f17) over Systolic.mirrorFoldPinched (426813b24)")
# The verifier's false red before 736f7ea44, kept verbatim so CLAUSE_REVISIONS can find it.
KO_FALSE_RED = ("; the verifier still reports it never produced, because its resolve strips a namespace prefix only when "
                "the prefix is a bare namespace token or a full namespace path, and kotowskiOllivier_closed writes its "
                "conclusion under the partial path Manuscript.NonMF.TheoremC (a classifier false red, reported to main)")
KO_RESOLVED = (", and the verifier resolves that producer since its fix at 736f7ea44 completes the partial path "
               "Manuscript.NonMF.TheoremC")
KO_CLOSED = KO_PRODUCED + KO_RESOLVED
BRIDGE_CLOSED = ("hbridge: RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement is closed by "
                 "HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed (#audit_closed_axioms, root-imported, "
                 "18682110d) over HullSC.quotientPeripheralLetterPullbackStatement_holds (#audit_closed_axioms, "
                 "root-imported)")
HW_CLOSED = ("hW: FinitelyPresentedInfiniteSimpleStatement (Hyde-Lodha) is closed by "
             "HydeLodha.finitelyPresentedInfiniteSimple_closed (#audit_closed_axioms)")
# Root reachability of the Lemma 9.4 modules over origin's import graph, checked at the merge launch: the pieces were
# root-imported at ROOTED_AT, and the modules called unreachable are not root-reachable at UNROOTED_AT.
ROOTED_AT = "e0dcf8b99"
UNROOTED_AT = "b58ece98f"
# The root wiring that imports OsinLemma94ShortSides and OsinLemma94OneCellValue (OsinUnboundCaseOneRun stays unreachable).
WIRED_AT = "80007c036"
R_WIRED = "the root wiring " + WIRED_AT + " imports OsinLemma94ShortSides and OsinLemma94OneCellValue"
PENDANT_PRODUCED = ("pendantPathRemovalInput (#audit_axioms, OsinLemma94PendantRemoval, 61c2ade8e, root-imported at "
                    "9eba4d854)")
CORNER_PRODUCED = "cornerInsertionInput (#audit_axioms, OsinLemma94CornerInsertion, f7538e223)"
PLANAR_FOR_0913 = "four planar pieces for osinLemma94Section_of_planarPieces (80790fad1, root-imported at 559636b4a)"
# The residual pieces as registered before f04929ebb, kept verbatim so CLAUSE_REVISIONS can find them.
PLANAR_FOR_TAIL_1500 = ("of which Case 1 has a producer and the count reduces to the side budget "
                        "OsinLemma94PolygonSideBudgetInput, the one piece not yet produced)")
PLANAR_FOR_TAIL = ("of which Case 1 reduces to the same-cell binder OsinLemma94CaseOneSameCellStatement and the count to "
                   "the side budget OsinLemma94PolygonSideBudgetInput and the same-cell premise "
                   "OsinLemma94UnboundSameCellStatement of the covering half, none of them produced yet)")
PLANAR_FOR = ("four planar pieces for osinLemma94Section_of_planarPieces (80790fad1, root-imported at 559636b4a; "
              "osinLemma94Section_of_residuals, #audit_axioms, OsinLemma94SectionResiduals, 0087a5095, 409bbbf72, 4002b9371, "
              "supplies the closed metric half, realization and Case 2 pieces and takes the count and Case 1 pieces, "
              + PLANAR_FOR_TAIL)
GREEN_RESIDUAL = ("the residual is hgreendlinger (GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement), not "
                  "yet produced: its producers bind Osin's Lemma 9.4 (OsinLemma94SectionStatement) with the pocket inputs, "
                  "Osin's Lemma 9.7, or the historical RelativeGreendlingerQuasiGeodesicStatement, and Lemma 9.4 stands over "
                  "the closed metric half and a diagram half not yet produced, OsinLemma94PlanarRunInput for "
                  "osinLemma94Section_of_pieces or " + PLANAR_FOR)
GREEN_FORMS = ("the forms over hgreendlinger alone are TorsionFreeGreendlingerLeaf.*_of_greendlinger (1edf0f7b4), "
               "TheoremC.manuscriptTorsionFree*_of_greendlinger (c5f953323), HullSC.*_of_greendlinger and "
               "TorsionFreeGreendlingerSentences.manuscriptSentence_*_of_greendlinger (2aa98f8cc), and "
               "HullCorollary74.printedHullCorollary74_of_greendlinger (c6e0b6c33), all root-imported at 559636b4a")
# The count piece as registered before 9f8779c4e moved K after eps, kept verbatim so CLAUSE_REVISIONS can find it.
COUNT_PIECE_0913 = ("OsinLemma94PolygonCountInput (a side budget K chosen before eps, over-strong as stated and ruled to move "
                    "after eps, and a slack L chosen after; reduced to the side budget OsinLemma94PolygonSideBudgetInput by "
                    "osinLemma94PolygonCountInput_of_sideBudget over the closed covering half osinLemma94PolygonCoversInput, "
                    "L = 24 eps, #audit_closed_axioms, 2b2e16cc6; hull-count94)")
SIDE_BUDGET_0913 = ("the side budget is not yet produced and, with K chosen before eps, over-strong as stated (a short region "
                    "side can cut off many two-sided pockets, and a quasi-geodesic boundary can carry spaced spurs); ruled F1: "
                    "K moves after eps in the count and metric Props, in one co-probed landing")
SIDE_BUDGET_OPEN = ("the side budget is not yet produced; K is chosen after eps since 9f8779c4e (ruled F1), and summed over "
                    "every maximal polygon the budget is over-strong as stated, since a G-face reading a value-one subword of "
                    "the boundary, such as a bubble on a spur of a section, is a polygon with no (A1) side and there can be "
                    "arbitrarily many of them with n = 1 (the model test in its docstring); the ruled patch counts classes, "
                    "maximal runs of consecutive cell sides whose gaps have value one, over polygons with an (A1) side, passes "
                    "audit-intro's pinched-cell model test, and respells the covering half over the class word, the dartWord of "
                    "the reversed cell arc, with L = 24 eps + 2 (K + 24) ceil((c + 2) / lambda), in one co-probed landing not "
                    "yet made; the (A3) short sides number at most 2 eps |M| by "
                    "OsinLemma94RealizedPolygons.sum_card_shortSides_le (#audit_axioms, OsinLemma94ShortSides, 4b6dd3cd8, "
                    "root-imported at " + WIRED_AT + "), and at most 24 eps n when |M| <= 3 (n + r - 1)")
# The covering half as registered before f04929ebb gave osinLemma94PolygonCoversInput its same-cell premise, in the count
# piece and in the side-budget rule, kept verbatim so CLAUSE_REVISIONS can find them.
COVERS_0913 = "over the closed covering half osinLemma94PolygonCoversInput, L = 24 eps, #audit_closed_axioms, 2b2e16cc6"
SIDE_COVERS_0913 = "over the closed covering half osinLemma94PolygonCoversInput (L = 24 eps, #audit_closed_axioms, 2b2e16cc6)"
COVERS = ("over the covering half osinLemma94PolygonCoversInput (L = 24 eps, #audit_axioms, OsinLemma94PolygonCount, "
          "2b2e16cc6, f04929ebb, root-imported), which takes hsame : OsinLemma94UnboundSameCellStatement (no unbound dart "
          "has its own cell across), an open residual that nothing produces yet, owner hull-count94 (class route, with "
          "ghw-charp2's respell)")
R_SAME = ("since f04929ebb osinLemma94CaseOneInput_of_walk and osinLemma94PolygonCoversInput take same-cell premises "
          "(lead ruling 09-13 16:00)")
COUNT_PIECE = ("OsinLemma94PolygonCountInput (a side budget K and a slack L, both chosen after eps; reduced to the side budget "
               "OsinLemma94PolygonSideBudgetInput by osinLemma94PolygonCountInput_of_sideBudget " + COVERS + "; "
               + SIDE_BUDGET_OPEN + "; sec5-sentences with hull-count94)")
# The four planar pieces as registered before 09-13 13:30, kept verbatim so CLAUSE_REVISIONS can find them.
PLANAR_NONE_0913 = "four pieces over dart-minimal optimal families, none yet produced: "
PLANAR_REALIZATION_0913 = ("OsinLemma94PolygonRealizationInput (a dart-minimal optimum has maximal component polygons, "
                           "OsinLemma94RealizedPolygons on the unselected G-faces; hull-unbound)")
CASE_ONE_0913 = "OsinLemma94CaseOneInput (no backwards connector pair onto a side that is not cutting; theoremc-retire)"
CASE_TWO_0913 = "OsinLemma94CaseTwoInput (none onto a cutting side; sec5-sentences)"
PLANAR_SOME = "four pieces over dart-minimal optimal families, three of them produced: "
PLANAR_REALIZATION = ("OsinLemma94PolygonRealizationInput (a dart-minimal optimum has maximal component polygons, "
                      "OsinLemma94RealizedPolygons on the unselected G-faces; closed by osinLemma94PolygonRealizationInput, "
                      "#audit_closed_axioms, OsinLemma94SectionResiduals, 4002b9371, which applies "
                      "osinLemma94PolygonRealizationInput_of_partition, #audit_axioms, 0087a5095, to the closed partition "
                      "osinLemma94PolygonPartitionInput, #audit_closed_axioms, OsinLemma94PolygonPartition, 746028b24, both "
                      "modules root-imported at " + ROOTED_AT + "; hull-unbound, ghw-assembly)")
# Case 1 as registered before f04929ebb gave osinLemma94CaseOneInput_of_walk its same-cell premise, kept verbatim so
# CLAUSE_REVISIONS can find it.
CASE_ONE_1500 = ("OsinLemma94CaseOneInput (no backwards connector pair onto a side that is not cutting; produced by "
            "osinLemma94CaseOneInput_of_walk, #audit_axioms, OsinUnboundCaseOneRun, 5be5cb6fc, not root-reachable at "
            + UNROOTED_AT + ", from osinLemma94CaseOneWalk, #audit_axioms, OsinLemma94CaseOneWalkHolds, eb9010962, "
            "root-imported, though no declaration composes the two, since ghw-charp2's census patch 10(f), not yet "
            "landed, adds hkind to osinLemma94CaseOne_false_of_walk and deletes _of_walk; the one-cell connector pairs "
            "then stay the same-cell binder OsinLemma94CaseOneSameCellStatement of "
            "osinLemma94CaseOneInput_of_walk_of_sameCell (3292f7a20), where a pocket with no relator cell is refuted by "
            "false_of_cellFree_pocket_X and _Y (#audit_axioms, OsinLemma94OneCellValue, ea9016135, root-imported at "
            + WIRED_AT + ") and a pocket with a relator cell needs Osin's loop case under OsinLemma97Below; "
            "theoremc-retire, ko-closed, jacobson)")
CASE_ONE = ("OsinLemma94CaseOneInput (no backwards connector pair onto a side that is not cutting; open: "
            "osinLemma94CaseOneInput_of_walk (#audit_axioms, OsinUnboundCaseOneRun, 5be5cb6fc, f04929ebb, root-reachable "
            "through OsinGreendlingerOpenResiduals) proves it from osinLemma94CaseOneWalk (#audit_axioms, "
            "OsinLemma94CaseOneWalkHolds, eb9010962, root-imported) and hsame : OsinLemma94CaseOneSameCellStatement, the "
            "one-cell connector pairs, not yet produced, and OsinGreendlingerOpenResiduals applies it at "
            "osinLemma94CaseOneWalk over its own hsameOne; in the same-cell binder a pocket with no relator cell is refuted "
            "by false_of_cellFree_pocket_X and _Y (#audit_axioms, OsinLemma94OneCellValue, ea9016135, root-imported at "
            + WIRED_AT + ") and false_of_sameCell_cellFree_pocketRegion_X and _Y (OsinLemma94SameCellCellFree, 29c1eeae3, "
            "not root-imported), and a pocket with a relator cell needs Osin's loop case under OsinLemma97Below; owner "
            "jacobson (binder 3), with theoremc-retire and ko-closed)")
CASE_TWO = ("OsinLemma94CaseTwoInput (none onto a cutting side; closed by osinLemma94CaseTwoInput, #audit_closed_axioms, "
            "OsinLemma94CaseTwo, e0e94015d, which applies osinLemma94CaseTwoInput_of_insertion, #audit_axioms, 52b77f408, to "
            "separatedCornerInsertionInput, #audit_closed_axioms, OsinLemma94SeparatedInsertionProof, 619b70139, both "
            "modules root-imported at " + ROOTED_AT + "; sec5-sentences)")
PLANAR_PIECES = ("osinLemma94Section_of_planarPieces (#audit_axioms, 80790fad1, root-imported at 559636b4a) proves "
                 "OsinLemma94SectionStatement from the closed metric half and " + PLANAR_SOME + PLANAR_REALIZATION + ", "
                 + COUNT_PIECE + ", " + CASE_ONE + " and " + CASE_TWO)

# The realization pieces of Lemma 9.4 as registered before 09-13 13:30, kept verbatim so CLAUSE_REVISIONS can find them.
REAL_NONE_0913 = "from four pieces, none yet produced: "
CUTTING_0913 = ("OsinLemma94CuttingChainsInput (with the fewest darts the cutting chains are (lambda, c + 2)-quasi-geodesic, "
                "from ChainRespellInput, PendantPathRemovalInput and QuasiGeodesicRespellInput; hull-unbound)")
CELL_0913 = "OsinLemma94CellArcsInput (relator arcs, from the C-condition; hull-unbound)"
BOUNDARY_0913 = "OsinLemma94BoundaryArcsInput (arcs of the boundary inside one section; hull-unbound)"
PARTITION_0913 = "OsinLemma94PolygonPartitionInput (the face walks split into maximal sides; ghw-assembly)"
REAL_SOME = "from four pieces, all produced: "
CUTTING = ("OsinLemma94CuttingChainsInput (with the fewest darts the cutting chains are (lambda, c + 2)-quasi-geodesic; "
           "derived by osinLemma94CuttingChainsInput_of_pieces, #audit_axioms, OsinLemma94CuttingChains, 108236c25, from "
           "ChainRespellInput, PendantPathRemovalInput and QuasiGeodesicRespellInput, all produced, the last by "
           "quasiGeodesicRespellInput, #audit_axioms, OsinLemma94QuasiGeodesicRespell, bbb8585ab; hull-unbound)")
CELL = ("OsinLemma94CellArcsInput (relator arcs, from the C-condition; produced by osinLemma94CellArcsInput_holds, "
        "#audit_axioms, OsinLemma94CellArcs, 5e5a98049; ko-closed)")
BOUNDARY = ("OsinLemma94BoundaryArcsInput (arcs of the boundary inside one section; closed by osinLemma94BoundaryArcsInput, "
            "#audit_closed_axioms, OsinLemma94BoundaryArcs, 1b453429f; cite-hull)")
PARTITION = ("OsinLemma94PolygonPartitionInput (the face walks split into maximal sides; closed by "
             "osinLemma94PolygonPartitionInput, #audit_closed_axioms, OsinLemma94PolygonPartition, 746028b24, over "
             "OsinLemma94PolygonMaximal, 9f03bfcd3, and osinLemma94PolygonRealizationInput, #audit_closed_axioms, "
             "OsinLemma94SectionResiduals, 4002b9371, applies osinLemma94PolygonRealizationInput_of_partition, "
             "#audit_axioms, 0087a5095, to it; ghw-assembly)")

# The respelling pieces and root reachability as registered before 09-13 13:30, kept verbatim for CLAUSE_REVISIONS.
CHAIN_HEAD_0913 = 'is minimal"), open: chainRespellInput_of_pieces'
CHAIN_OPEN_0913 = "CornerInsertionInput and PendantPathRemovalInput are not yet produced; "
REACH_CHAIN_0913 = ("OsinLemma94ChainRespell, OsinLemma94SeparatingRemoval and OsinLemma94PolygonRealization are not "
                    "root-reachable at 94c3c98eb")
REACH_COUNT_0913 = "OsinLemma94PolygonCount is not root-reachable at 94c3c98eb"
REACH_REAL_0913 = "OsinLemma94PolygonRealization is not root-reachable at 94c3c98eb"
CHAIN_HEAD = 'is minimal"), derived: chainRespellInput_of_pieces'
CHAIN_PRODUCED = ("CornerInsertionInput is produced by " + CORNER_PRODUCED + " and PendantPathRemovalInput by "
                  + PENDANT_PRODUCED + ", so SeparatingPathRemovalInput and ChainRespellInput are produced; ")
REACH_CHAIN = ("OsinLemma94ChainRespell, OsinLemma94SeparatingRemoval and OsinLemma94PolygonRealization are root-imported "
               "at 65d0a4497, and OsinLemma94CornerInsertion at " + ROOTED_AT)
REACH_COUNT = "OsinLemma94PolygonCount is root-imported at 65d0a4497"
ROOTED_PIECES = ("OsinLemma94CornerInsertion, OsinLemma94CuttingChains, OsinLemma94QuasiGeodesicRespell, "
                 "OsinLemma94CellArcs, OsinLemma94BoundaryArcs, OsinLemma94PolygonPartition, OsinLemma94PolygonMaximal and "
                 "OsinLemma94SectionResiduals are root-imported at " + ROOTED_AT)
REACH_REAL = "OsinLemma94PolygonRealization is root-imported at 65d0a4497, and " + ROOTED_PIECES

# The GFaceMerge blind spot as registered before the verifier fix, kept verbatim for CLAUSE_REVISIONS.
GFM_0913 = ("separatingPathRemovalInput_of_pendant builds its merge in place with an anonymous constructor, and the "
            "root-imported OsinLemma94DartMinimal obtains merges in place as well, which the verifier's producer index does "
            "not see (the CutLift blind spot, reported to main; systolic-counts owns the verifier fix)")
GFM = ("separatingPathRemovalInput_of_pendant builds its merge as the witness of an obtain over an existential "
       "(OsinLemma94SeparatingRemoval.lean:89), and the root-imported OsinLemma94DartMinimal obtains merges the same way "
       "(lines 81 and 126), which the verifier's producer index still does not see after its fix at 736f7ea44 (a residual "
       "classifier blind spot, reported to systolic-counts)")
WALLS = ("of the four walls of sec:torsion-free three are closed, " + KO_CLOSED + "; " + BRIDGE_CLOSED + "; "
         + HW_CLOSED + "; " + GREEN_RESIDUAL + "; " + GREEN_FORMS)
GREEN_OWNERS = "owners hull-unbound, hull-count94, theoremc-retire, sec5-sentences (the Lemma 9.4 pieces), hull-respell"
SYSTOLIC_LEAVES = ("its systolic leaves all have producers: hzip CCKW.zipSpur_cosetComplex (#audit_closed_axioms), hfold "
                   "Systolic.mirrorFold and hpinch Systolic.mirrorFoldPinched (426813b24), hT6 systolicInvariantClique "
                   "(CCKWSystolicInvariantCliqueClosed, #audit_axioms, 84e93eebd, root-imported at 559636b4a)")

# The leads registered while the verifier named hKO as the open premise (before 736f7ea44), kept verbatim for
# CLAUSE_REVISIONS; since the fix the verifier reports hgreendlinger alone on those declarations.
HKO_LEAD_0913 = "the hKO wall (TheoremC.KotowskiOllivierStatement) reduced over GHB(7) to systolic leaves; "
HW_LEAD_0913 = "the open predicate is TheoremC.KotowskiOllivierStatement, fed to Fournier-Facio's G_0 beside hW; "
G0_LEAD_0913 = ("Fournier-Facio's G_0 is fed by TheoremC.KotowskiOllivierStatement (a torsion-free hyperbolic property-(T) "
                "group); ")
GREEN_ALONE = ("the verifier reports hgreendlinger (GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement) alone "
               "since its fix at 736f7ea44, and ")
HKO_LEAD = (GREEN_ALONE + "the hKO wall (TheoremC.KotowskiOllivierStatement), reduced over GHB(7) to systolic leaves, is "
            "closed; ")
HW_LEAD = GREEN_ALONE + "TheoremC.KotowskiOllivierStatement, which feeds Fournier-Facio's G_0 beside hW, is closed; "
G0_LEAD = (GREEN_ALONE + "the torsion-free hyperbolic property-(T) group that feeds Fournier-Facio's G_0 "
           "(TheoremC.KotowskiOllivierStatement) is closed; ")

HKO_WHY = ("the premise is a systolic leaf of the hKO wall (TheoremC.KotowskiOllivierStatement, reduced over GHB(7)); "
           + SYSTOLIC_LEAVES + "; " + WALLS + "; " + GREEN_OWNERS)
HKO_CHAIN_WHY = ("an intermediate step of the closed hKO chain, cited beside "
                 "KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed (#audit_closed_axioms, root-imported, "
                 "f65f99f17); " + SYSTOLIC_LEAVES + "; owners ko-closed, kh-cckw")
HW_WHY = HW_LEAD + WALLS + "; " + GREEN_OWNERS
FFF_WHY = ("the row's producers of the Fournier-Facio paragraph (FFF S2: fournierFacioParagraph_of_literatureInputs, "
           "_of_leastAreaLeaves, _of_fourLeaves, _of_greendlinger) bind TheoremC.LiteratureInputs or its leaves; " + WALLS
           + "; " + GREEN_OWNERS)
G0_WHY = ("the premise TheoremC.KotowskiOllivierStatement (a torsion-free hyperbolic property-(T) group) feeds "
          "Fournier-Facio's G_0; " + WALLS + "; " + GREEN_OWNERS)
HHARD_WHY = ("premise hhard, for every group G the implication IsAcylindricallyHyperbolicLimitSet G -> "
             "IsAcylindricallyHyperbolicOsin G, is a statement written inline, not a citation: it is the hard direction of "
             "the limit-set spelling of \"acylindrically hyperbolic\" in sec:torsion-free, proved by "
             "GGT.OsinClassification.isAcylindricallyHyperbolicOsin_of_limitSet (#audit_axioms, OsinLimitSetSpelling, "
             "3f71a3a50, root-imported), which the sibling carriers apply: "
             "HullCitationSentences.printedHullGeneratingSetLimitSet (#audit_closed_axioms, root-imported) and "
             "TorsionFreeGreendlingerForms.manuscriptSaturationLimitSet_of_greendlinger, whose only binder is hgreendlinger; "
             "owners sec5-sentences, hull-bridge")
LEAST_AREA_WHY = ("over the least-area leaves of Hull Theorem 7.1 (RelativeGreendlingerQuasiGeodesicLeastAreaStatement and "
                  "RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement); " + BRIDGE_CLOSED + "; " + GREEN_RESIDUAL
                  + "; " + GREEN_FORMS + "; " + GREEN_OWNERS)
PIECES_WHY = ("Osin's Lemma 9.4 over two named pieces inside the least-area Hull 7.1 route: osinLemma94Section_of_pieces "
              "derives OsinLemma94SectionStatement from the metric half OsinLemma94AntiparallelMetricStatement, closed by "
              "osinLemma94AntiparallelMetric (#audit_closed_axioms, e3da1ba60), and the diagram half "
              "OsinLemma94PlanarRunInput (component polygons carrying the unbound darts with no backwards connector pair, "
              "Osin's Cases 1 and 2), not yet produced, so the only residual of this route is OsinLemma94PlanarRunInput; "
              "the parallel route " + PLANAR_PIECES + "; the reduced route over OsinLemma94PlanarRunInputReduced "
              "(88db0df7b) was retired at b6bda9923")
PLANAR_PIECES_WHY = ("Osin's Lemma 9.4 over four planar pieces inside the least-area Hull 7.1 route: " + PLANAR_PIECES
                     + "; GloballyDistinguishedSectionFamily.DartMinimal is the Case 2 measure (the fewest darts among the "
                     "optimal families with the same unbound sum, in place of Osin's minimal total length of the cutting "
                     "paths), a hypothesis of each piece and not an open carrier: exists_dartMinimal (#audit_axioms, "
                     "80790fad1) replaces any optimal family by a dart-minimal one with the same number of regions and "
                     "unbound sum, and exists_reduced_dartMinimal (#audit_axioms, OsinLemma94DartMinimal, b6bda9923, "
                     "root-imported at 559636b4a) makes it also merged across edges and split at pinches; owners "
                     "hull-unbound, hull-count94, theoremc-retire, sec5-sentences")
L44_WHY = ("Hull's Lemma 4.4 and one-step quotient statements, produced only over the least-area leaves of Hull Theorem 7.1 "
           "(HullSC.hullTowerStatementGeneral_of_leastAreaLeaves and the *_of_greendlinger forms); " + BRIDGE_CLOSED + "; "
           + GREEN_RESIDUAL + "; " + GREEN_FORMS + "; " + GREEN_OWNERS)
L44_WHY_0913 = ("Hull's Lemma 4.4 and one-step quotient statements, produced only from the open Theorem 7.1 leaves; owners "
                "hull-respell, hull-bridge, sec5-sentences")
COR74_CARRIER_WHY = ("the printed statement of Hull Corollary 7.4 (G_0 as a common quotient of two acylindrically "
                     "hyperbolic groups), proved at the printed generality by HullCorollary74.printedHullCorollary74_of_tower "
                     "(#audit_axioms, c6e0b6c33, root-imported at 559636b4a) from HullSC.HullTowerStatementGeneral, and over "
                     "hgreendlinger alone by printedHullCorollary74_of_greendlinger; " + BRIDGE_CLOSED + "; "
                     + GREEN_RESIDUAL + "; owner cite-hull; " + GREEN_OWNERS)
COR74_HYP_WHY = ("a printed hypothesis, not a conditional: E and H with trivial finite radical, their Hull generating sets, "
                 "E finitely generated and H countable are the hypotheses of the lemma's case E, H in AH_0; "
                 "HullCorollary74.printedHullCorollary74_of_tower supplies them at G_i/K(G_i) through "
                 "HullLemma510.printedHullLemma510 and exists_hullGeneratingSet, and the lemma's only corpus premise is "
                 "htower (HullSC.HullTowerStatementGeneral); owner cite-hull")
CARRIER_WHY = ("the printed statement named as vocabulary beside the leaf-conditional producers the rows cite; " + WALLS
               + "; " + GREEN_OWNERS)


def hko_why(decl):
    return HKO_CHAIN_WHY if "KotowskiOllivierClosed" in decl else HKO_WHY


# The texts registered before 09-13 07:40, kept verbatim so REVISIONS can find them.
HKO_WHY_0913 = ("the hKO wall (TheoremC.KotowskiOllivierStatement) reduced over GHB(7) to three systolic leaves: hzip is "
                "closed (Systolic.zipSpurStatement from Systolic.zipPinchStatement; CCKW.zipSpur_cosetComplex, "
                "#audit_closed_axioms), while Systolic.MirrorFoldStatement on CCKW.cosetComplex (hfold) and "
                "CCKW.SystolicInvariantCliqueStatement (hT6) are not yet produced; owners fff-periodic (hfold), "
                "kh-cckw (hT6), ko-closed")
HW_WHY_0913 = ("the hW premise (FinitelyPresentedInfiniteSimpleStatement, Hyde-Lodha) has the closed producer "
               "HydeLodha.finitelyPresentedInfiniteSimple_closed (#audit_closed_axioms); the declaration still binds the "
               "open least-area Hull 7.1 leaves (hgreendlinger, hbridge) and TheoremC.KotowskiOllivierStatement; owners "
               "hull-select, hull-bridge, fff-periodic, kh-cckw, ko-closed")
FFF_WHY_0913 = ("the row's producers of the Fournier-Facio paragraph (FFF S2: fournierFacioParagraph_of_literatureInputs, "
                "_of_leastAreaLeaves, _of_fourLeaves) bind TheoremC.LiteratureInputs or its open leaves, the least-area "
                "Hull 7.1 leaves and TheoremC.KotowskiOllivierStatement; their hW premise is closed as "
                "HydeLodha.finitelyPresentedInfiniteSimple_closed; owners hull-select, hull-bridge, fff-periodic, "
                "kh-cckw, ko-closed")
G0_WHY_0913 = ("Fournier-Facio's G_0 is fed by TheoremC.KotowskiOllivierStatement (a torsion-free hyperbolic property-(T) "
               "group), not yet produced; owners kh-hyperbolic, kh-torsion")
LEAST_AREA_WHY_0913 = ("over the least-area leaves of Hull Theorem 7.1 (RelativeGreendlingerQuasiGeodesicLeastAreaStatement, "
                       "RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement and its letter pullback), not yet "
                       "produced; owners hull-select, hull-unbound, hull-bridge, sec5-sentences")
PIECES_WHY_0913 = ("Osin's Lemma 9.4 over two named pieces inside the least-area Hull 7.1 route: "
                   "osinLemma94Section_of_pieces derives OsinLemma94SectionStatement from the metric half "
                   "OsinLemma94AntiparallelMetricStatement, closed by osinLemma94AntiparallelMetric (#audit_closed_axioms, "
                   "e3da1ba60), and the diagram half OsinLemma94PlanarRunInput (component polygons carrying the unbound "
                   "darts with no backwards connector pair, Osin's Cases 1 and 2), not yet produced; the only residual is "
                   "OsinLemma94PlanarRunInput; owner hull-unbound")
CARRIER_WHY_0913 = ("the printed statement named as vocabulary beside the leaf-conditional producers the rows cite; it is "
                    "produced only through the open Hull 7.1 and FFF S2 leaves; owners sec5-sentences, hull-*, "
                    "simple-group, kh-*")

# A justification that was true when registered and is no longer true is rewritten in place; the (kind, declaration)
# key stays, so the verifier's accepted set does not change.  new_why may be a function of the declaration.
REVISIONS = [
    ("the hKO wall (TheoremC.KotowskiOllivierStatement) reduced over GHB(7) to three systolic leaves "
     "(Systolic.ZipSpurStatement, whose fold case is closed and whose pinch case is Systolic.ZipPinchStatement; "
     "Systolic.MirrorFoldStatement on CCKW.cosetComplex; CCKW.SystolicInvariantCliqueStatement), not yet produced; "
     "owners kh-torsion (hzip), fff-periodic (hfold), kh-cckw (hT6), ko-closed", hko_why, "hzip closed"),
    ("FFF S2 needs a finitely presented torsion-free infinite simple group (FinitelyPresentedInfiniteSimpleStatement, "
     "Hyde-Lodha), not yet produced; owner simple-group", HW_WHY, "hW closed"),
    ("the Fournier-Facio paragraph (FFF S2) is produced only through TheoremCAssembly's open admissions until "
     "KotowskiOllivierStatement and FinitelyPresentedInfiniteSimpleStatement are proved; owners simple-group, "
     "kh-hyperbolic, kh-torsion", FFF_WHY, "TheoremCAssembly producers deleted at 2c3c8cb40, hW closed"),
    (HKO_WHY_0913, hko_why, "hfold, hpinch and hKO closed (426813b24, f65f99f17), hbridge closed (18682110d)"),
    (HW_WHY_0913, HW_WHY, "hKO closed (f65f99f17), hbridge closed (18682110d)"),
    (FFF_WHY_0913, FFF_WHY, "hKO closed (f65f99f17), hbridge closed (18682110d)"),
    (G0_WHY_0913, G0_WHY, "hKO closed (f65f99f17)"),
    (LEAST_AREA_WHY_0913, LEAST_AREA_WHY, "hbridge closed (18682110d)"),
    (PIECES_WHY_0913, PIECES_WHY, "the planar half split into four pieces (80790fad1)"),
    (CARRIER_WHY_0913, CARRIER_WHY, "hKO closed (f65f99f17), hbridge closed (18682110d)"),
    (L44_WHY_0913, L44_WHY, "hbridge closed (18682110d)"),
]
revised = 0
for i, line in enumerate(out):
    m = entry.match(line)
    if not m:
        continue
    for old, new_why, reason in REVISIONS:
        if old in line:
            why = new_why(m.group("decl")) if callable(new_why) else new_why
            out[i] = line.replace(old, why) + " [revised by the census merge at %s: %s]" % (sha9, reason)
            revised += 1
            break

# A clause that went stale while the rest of its justification stands is rewritten wherever it occurs; the line records
# one revision for all of them.
ROOT_WIRED = ("OsinLemma94PlanarPieces, OsinLemma94DartMinimal, CCKWSystolicInvariantCliqueClosed and the "
              "_of_greendlinger form modules root-imported at 559636b4a")
# The reasons the Lemma 9.4 revisions record, and the rule-text clauses they rewrite that no constant above holds.
R_COUNT = "the Lemma 9.4 side constant chosen after eps (9f8779c4e) and the side budget patch ruled"
R_RESIDUALS = ("the Lemma 9.4 residual assembly osinLemma94Section_of_residuals takes only the count and Case 1 "
               "(0087a5095, 409bbbf72, 4002b9371)")
R_CASES = "Case 1 of Lemma 9.4 has a producer (5be5cb6fc) and Case 2 is closed (e0e94015d)"
R_REALIZATION = "the Lemma 9.4 realization is closed over the partition (746028b24, 4002b9371)"
R_PIECES = "the respelling, cutting-chain and arc pieces of Lemma 9.4 have producers"
R_REACH = "the Lemma 9.4 surgery modules root-imported at 65d0a4497"
REAL_HEAD_0913 = "polygon), open: osinLemma94PolygonRealizationInput_of_pieces"
REAL_HEAD = "polygon), derived: osinLemma94PolygonRealizationInput_of_pieces"
COUNT_OWNER_0913 = "; owner hull-count94"
COUNT_OWNER = "; owners hull-count94, sec5-sentences"
CLAUSE_REVISIONS = [
    ("80790fad1, not root-imported)", "80790fad1, root-imported at 559636b4a)", ROOT_WIRED),
    ("OsinLemma94DartMinimal, b6bda9923, not root-imported)", "OsinLemma94DartMinimal, b6bda9923, root-imported at 559636b4a)",
     ROOT_WIRED),
    ("CCKWSystolicInvariantCliqueClosed, #audit_axioms, 84e93eebd, not root-imported)",
     "CCKWSystolicInvariantCliqueClosed, #audit_axioms, 84e93eebd, root-imported at 559636b4a)", ROOT_WIRED),
    ("printedHullCorollary74_of_greendlinger (c6e0b6c33), none root-imported yet",
     "printedHullCorollary74_of_greendlinger (c6e0b6c33), all root-imported at 559636b4a", ROOT_WIRED),
    ("OsinLemma94PolygonCountInput (a side budget K chosen before eps and a slack L chosen after; hull-count94)",
     COUNT_PIECE, "the covering half of the Lemma 9.4 count closed (2b2e16cc6)"),
    (KO_FALSE_RED, KO_RESOLVED, "the verifier fix 736f7ea44 completes partial namespace paths"),
    (HKO_LEAD_0913, HKO_LEAD, "since 736f7ea44 the verifier reports hgreendlinger alone on these declarations"),
    (HW_LEAD_0913, HW_LEAD, "since 736f7ea44 the verifier reports hgreendlinger alone on these declarations"),
    (G0_LEAD_0913, G0_LEAD, "since 736f7ea44 the verifier reports hgreendlinger alone on these declarations"),
    (COUNT_PIECE_0913, COUNT_PIECE, R_COUNT),
    (SIDE_BUDGET_0913, SIDE_BUDGET_OPEN, R_COUNT),
    (PLANAR_FOR_0913, PLANAR_FOR, R_RESIDUALS),
    (PLANAR_NONE_0913, PLANAR_SOME, R_CASES),
    (PLANAR_REALIZATION_0913, PLANAR_REALIZATION, R_REALIZATION),
    (CASE_ONE_0913, CASE_ONE, R_CASES),
    (CASE_TWO_0913, CASE_TWO, R_CASES),
    (REAL_HEAD_0913, REAL_HEAD, R_REALIZATION),
    (REAL_NONE_0913, REAL_SOME, R_REALIZATION),
    (CUTTING_0913, CUTTING, R_PIECES),
    (CELL_0913, CELL, R_PIECES),
    (BOUNDARY_0913, BOUNDARY, R_PIECES),
    (PARTITION_0913, PARTITION, R_REALIZATION),
    (CHAIN_HEAD_0913, CHAIN_HEAD, R_PIECES),
    (CHAIN_OPEN_0913, CHAIN_PRODUCED, R_PIECES),
    (REACH_CHAIN_0913, REACH_CHAIN, R_REACH),
    (REACH_COUNT_0913, REACH_COUNT, R_REACH),
    (REACH_COUNT + COUNT_OWNER_0913, REACH_COUNT + COUNT_OWNER, R_COUNT),
    (REACH_REAL_0913, REACH_REAL, R_REACH),
    (GFM_0913, GFM, "the verifier fix 736f7ea44 leaves the GFaceMerge obtain witnesses unseen"),
    ("(#audit_axioms, OsinLemma94ShortSides, 4b6dd3cd8, not root-reachable at b58ece98f)",
     "(#audit_axioms, OsinLemma94ShortSides, 4b6dd3cd8, root-imported at " + WIRED_AT + ")", R_WIRED),
    ("(#audit_axioms, OsinLemma94OneCellValue, ea9016135, not root-reachable at b58ece98f)",
     "(#audit_axioms, OsinLemma94OneCellValue, ea9016135, root-imported at " + WIRED_AT + ")", R_WIRED),
    (CASE_ONE_1500, CASE_ONE, R_SAME),
    (COVERS_0913, COVERS, R_SAME),
    (SIDE_COVERS_0913, COVERS, R_SAME),
    (PLANAR_FOR_TAIL_1500, PLANAR_FOR_TAIL, R_SAME),
]
for i, line in enumerate(out):
    if not entry.match(line):
        continue
    rewritten, reasons = line, []
    for old, why, reason in CLAUSE_REVISIONS:
        if old in rewritten:
            rewritten = rewritten.replace(old, why)
            if reason not in reasons:
                reasons.append(reason)
    if reasons:
        out[i] = rewritten + " [revised by the census merge at %s: %s]" % (sha9, "; ".join(reasons))
        revised += 1

DRB_PIECES = ("CoreRingReflectionStatement (thm:core-ring-reflection, owner chain-reflection), CoreModelsLEFStatement "
              "(lem:chain-core-models, owner chain-itinerary), CountableCrossedProductStatement (owner chain-core), "
              "CoreMFRadicalKillStatement (thm:core-mf-radical, owner chain-radical), BilateralThreeTransferStatement "
              "(prop:bilateral-three, owner ct-bilateral-mf), TorsionDefectTransferStatement (prop:torsion-defect-ring, "
              "closed over CountableCrossedProductStatement at aadb514ad), UnitKernelLocallyFiniteStatement and "
              "ReturnEmbeddingStatement (the return tower, the induced core and lem:involution-localization; owners "
              "ct-return-tower, ct-involution, ct-rank-budget)")

RULES = [
    (lambda d, det, dt: det == "carrier-data" and d.endswith(".DynamicRankBudget.PrintedDynamicRankBudget"),
     "cor:dynamic-rank-budget as printed (tex 1696-1705), open: PrintedDynamicRankBudget "
     "(Manuscript/NonMFSentences/DynamicRankBudget, a2cb17f58) is the named Prop of the printed corollary, produced only "
     "by printedDynamicRankBudget_of_pieces over the residual piece Props " + DRB_PIECES + "; each piece is a named Prop "
     "nothing produces yet, an open residual, not a citation; the module is not root-imported, so the rows citing it "
     "stay partial; owner ct-rank-budget (census successor, 2026-09-13)"),
    (lambda d, det, dt: det == "open-predicate" and d.endswith(".DynamicRankBudget.printedDynamicRankBudget_of_pieces"),
     "the printed proof of cor:dynamic-rank-budget (tex 1707-1766) over its residual piece Props, open: "
     "printedDynamicRankBudget_of_pieces (#audit_axioms, Manuscript/NonMFSentences/DynamicRankBudget, a2cb17f58) takes "
     + DRB_PIECES + "; each premise is a named Prop nothing produces yet, an open residual, not a citation; the rows "
     "citing it stay partial; owner ct-rank-budget (census successor, 2026-09-13)"),
    (lambda d, det, dt: re.search(r"FaceSetEarStatement|FaceSetEarDataStatement|RegionShellingStatement"
                                  r"|_of_earStatement|estimatingPieceConstruction_of_(ear|shelling)\b", d + " " + dt),
     "route refuted; W1 (a) is on the ofPlanar carrier: the premise is a false Prop, Embedded.FaceSetEarStatement and "
     "FaceSetEarDataStatement (refuted by not_faceSetEarStatement and not_faceSetEarDataStatement, #audit_closed_axioms, "
     "9dda53a05) or RegionShellingStatement (refuted by not_regionShellingStatement, #audit_closed_axioms, 3f6eaff76), "
     "so this producer is never discharged; the pocket piece is built by DiscDiagram.ofPlanar on an IsDiscRegion face "
     "set (lead ruling 09-13); owners kh-torsion, hull-select, kh-ejz, go-lemma42"),
    (lambda d, det, dt: det == "conditional-data" and re.search(r"HullSC\.(cutLiftOutcome|CutLift\.toCutMove)$", d),
     "not a conditional: HullSC.CutLift is a Prop structure, the certificate cut datum "
     "(HullSCLemma51LetterPullbackCutLift), and cutLiftOutcome and CutLift.toCutMove are lemmas about any cut lift "
     "(every cut lift has an outcome; a cut lift gives a cut move), both #audit_axioms; "
     "letterStepBound_of_cutLiftOutcome builds its cut lift in place with an anonymous constructor "
     "(HullSCLemma51LetterPullbackCut), which the verifier's producer index does not see (a classifier blind spot, "
     "reported to main); the chain ends in HullSC.quotientPeripheralLetterPullbackStatement_holds (#audit_closed_axioms, "
     "root-imported), which feeds HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed (#audit_closed_axioms, "
     "root-imported, 18682110d); owner hull-bridge"),
    (lambda d, det, dt: det == "buried-conditional" and re.search(
        r"HullSC\.(quotientPeripheralLetterPullbackStatement_holds|relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed)$",
        d),
     "not a conditional: the declaration binds nothing and is closed (#audit_closed_axioms, root-imported; the bridge at "
     "18682110d); the buried premises are the hypotheses of the Statement it proves, D.IsHyperbolicallyEmbedded "
     "(thm:hull's printed hypothesis, DGO Definition 4.25) and the least-area certificate premise, which each consumer "
     "supplies at its own D; owner hull-bridge"),
    (lambda d, det, dt: det == "conditional-data" and re.search(r"Surgery\.GFaceMerge\.(facePerm_keep_of_ne|sigma_keep_eq_self)$", d),
     "not a conditional: Surgery.GFaceMerge (SurgeryGFaceMerge, root-imported) is the datum of a G-face merge, a dart "
     "between two different non-exterior G-faces with no relator cell on either side, and facePerm_keep_of_ne (a dart "
     "off the deleted edge whose successor is off the edge keeps its successor) and sigma_keep_eq_self (the second dart "
     "of the path leaves a vertex of valence one) are lemmas about any merge, both #audit_axioms "
     "(OsinLemma94SeparatingRemoval, 7d4a2515f); " + GFM + "; owner hull-unbound"),
    (lambda d, det, dt: det == "buried-conditional" and d.endswith(".OsinLemma94ClassPolygons.dense_of_classCovers"),
     "not a conditional: dense_of_classCovers (#audit_axioms, OsinLemma94PolygonClasses, 6db79cea7, a25fe2383) is the "
     "arithmetic step of Osin's Lemma 9.4 (\"Assume that S >= n sqrt rho\"): if n sqrt rho <= S <= M sum S_i + L n, "
     "0 < M and rho >= 4 L^2, the class words are dense at floor(rho / (4 M^2)); its premise hcovers : Q.ClassCovers M L "
     "(S <= M sum S_i + L n) is a hypothesis about any class polygons Q, which its one caller unbound_lt_of_classes "
     "(#audit_axioms) passes on from its own hcovers; the cover itself is the open count residual "
     "OsinLemma94ClassCountInput, which nothing produces yet; OsinLemma94PolygonClasses is root-imported at 074e7a200; "
     "owner hull-count94"),
    (lambda d, det, dt: det == "buried-conditional" and d.endswith(".OsinLemma94ClassPolygons.unbound_lt_of_classes"),
     "Osin Lemma 9.4, the contradiction at fixed parameters over the classes (\"Assume that S >= n sqrt rho\"): "
     "unbound_lt_of_classes (#audit_axioms, OsinLemma94PolygonClasses, 6db79cea7, a25fe2383) derives S < n sqrt rho "
     "from its hypotheses; hbudget : Q.ClassBudget K and hcovers : Q.ClassCovers M L with 0 < M are the open count "
     "residual over the classes, OsinLemma94ClassCountInput, which nothing produces yet, and rho >= 4 M^2 rhom and "
     "rho >= 4 L^2 are the threshold; hmetric is OsinLemma94DensePolygonsAntiparallel at every rho' >= rhom, the instance "
     "of OsinLemma94AntiparallelMetricStatement (closed by osinLemma94AntiparallelMetric, #audit_closed_axioms, "
     "e3da1ba60); hcases refutes a backwards connector pair on the class words (Osin's Cases 1 and 2); no declaration "
     "applies unbound_lt_of_classes yet; OsinLemma94PolygonClasses is root-imported at 074e7a200; owner hull-count94"),
    (lambda d, det, dt: det == "carrier-data" and d.endswith(".OsinLemma94ClassCountInput"),
     "Osin Lemma 9.4 count piece over the classes, open: OsinLemma94ClassCountInput (OsinLemma94PolygonClasses, "
     "6db79cea7, a25fe2383) respells the count residual over classes of sides (maximal runs along one cell or one section "
     "of the boundary, value-one gaps included): for eps past a threshold there are K, M > 0 and L with Lemma 9.3 "
     "\"sum n_i <= 53 n\" and (38) \"k_i <= 4 n_i\" as one class budget K (ClassBudget) and S <= M sum S_i + L n "
     "(ClassCovers), under clause (b) of Lemma 9.7 for the least-area diagrams with fewer cells as a binder; it is a "
     "named Prop that nothing produces and no declaration consumes yet, an open residual, not a citation; "
     "unbound_lt_of_classes (#audit_axioms) derives the fixed-parameter contradiction from ClassBudget, ClassCovers, the "
     "metric half and the cases; OsinLemma94PolygonClasses is root-imported at 074e7a200; owner hull-count94"),
    (lambda d, det, dt: det == "carrier-data" and d.endswith(".OsinLemma94PinchedQuadrilateralStatement"),
     "Osin Lemma 9.4 Case 1 through pinched windows, member (a): OsinLemma94PinchedQuadrilateralStatement "
     "(OsinLemma94PinchedQuadrilateral, d463383fa, root-imported at c0c1a8e3d) is a named Prop (an inner face with no "
     "relator cell and in no selected region, reading X, the sides of an arc q, Y and the sides of an arc p of a "
     "different cell, where the gaps between sides read the identity, with legal words s1, s2 of length and norm at most "
     "eps with the values of X and Y, is a contradiction); nothing produces it, an open residual, not a citation; its "
     "docstring model-tests the route; lead ruling 09-13 16:00: both members stand, ko-closed consumes (a), and the "
     "producer owner is simple-group over fff-periodic's PinchSplit layer, consuming hair opening; owner hull-unbound"),
    (lambda d, det, dt: det == "open-predicate" and d.endswith(".OsinLemma94PinchedQuadrilateralStatement.false_of_quadrilateral"),
     "Osin Lemma 9.4 Case 1, one piece per arc: false_of_quadrilateral (#audit_axioms, OsinLemma94PinchedQuadrilateral, "
     "d463383fa, root-imported at c0c1a8e3d) specializes member (a) to arcs with no gap, the configuration of "
     "RealizedSectionFamily.false_of_quadrilateral_face; its premise h is the open Prop "
     "OsinLemma94PinchedQuadrilateralStatement, which nothing produces yet, and no declaration applies "
     "false_of_quadrilateral yet; owner hull-unbound"),
    (lambda d, det, dt: det == "buried-conditional" and d.endswith(".OsinLemma94PinchedQuadrilateralStatement.false_of_quadrilateral"),
     "not a conditional beyond h: false_of_quadrilateral (#audit_axioms) binds the open Prop h : "
     "OsinLemma94PinchedQuadrilateralStatement (registered as its open predicate), and hleast : Delta.LeastArea and "
     "hinv1, hinv2 (the letters of s1 and s2 have inverses in symmetricLabelAlphabet D) are Case 1's configuration "
     "hypotheses, which each caller holds; owner hull-unbound"),
    (lambda d, det, dt: re.search(r"\.(OsinLemma94KindTransitionInput|OsinLemma94LongTransitionInput"
                                  r"|osinLemma94KindTransitionInput_of_longTransitions"
                                  r"|OsinLemma94RealizedPolygons\.(KindJoins|card_shortAdjacent_le|card_kindNonJoins_le"
                                  r"|sum_card_kindNonJoins_le_mul|card_filter_not_le_kindNonJoins_add))$", d),
     "Osin Lemma 9.4, the kind transitions of the class count (row 4895f03fdf5f at 9c89ca5e8; OsinLemma94ClassTransitions, "
     "2767e402d, not root-imported): osinLemma94KindTransitionInput_of_longTransitions (#audit_axioms) proves "
     "OsinLemma94KindTransitionInput (at most K n kind non-joins over the polygons with an (A1) side, under the "
     "hypotheses of OsinLemma94ClassCountInput) with constant 48 eps + K from OsinLemma94LongTransitionInput (the same "
     "count for the long transitions alone); the short part is OsinLemma94RealizedPolygons.sum_card_kindNonJoins_le_mul "
     "(#audit_axioms), whose hcells and hcard each caller holds; OsinLemma94LongTransitionInput is the open residual "
     "(b), a named Prop that nothing produces, not a citation, and its docstring's model, a bubble pinched on one side "
     "around a G-face or a hair, needs the un-pinch surgery (hair opening, kh-cckw; bubble un-pinch, leavitt-units); "
     "owner sec5-sentences"),
    (lambda d, det, dt: ".Manuscript.ChainCore.BilateralThree." in d,
     "prop:bilateral-three and its Introduction clause, a scaffold (rows fcffb8d73, d3438883d, 947e1957a; "
     "BilateralThreeGroupKill at dfc4d5221, BilateralThreeStatement and BilateralThreeCorollaries, none root-imported at "
     "947e1957a): PrintedBilateralThree and PrintedIntroDirectlyFiniteIffGLThreeMF are named Props, proved by "
     "printedBilateralThree_of_pieces and printedIntroDirectlyFiniteIffGLThreeMF_of_printedBilateralThree (#audit_axioms) "
     "only from four piece Props that nothing produces yet, BilateralThreeCellStatement (ct-bilateral-cell), "
     "ClopenCrossedProductCountableStatement (chain-core S1), ClopenCrossedProductDirectlyFiniteLEFStatement "
     "(chain-reflection) and ClopenCrossedProductNonzeroDefectStatement (chain-matricial, chain-reflection), open "
     "residuals, not citations; rootThree_killed_of_cell and the group-level lemmas killed_of_commutators, "
     "killed_of_finite_central_defect and root_killed_of_finite_central_defect (#audit_axioms) take the printed "
     "relations of the cell as hypotheses, which BilateralThreeCellStatement supplies; defectIdeal and clopenDefectSet "
     "are constructions (the ideal of the clopen defects) and MFTargetsKillRelativeElementary is the printed kill "
     "clause; hasKazhdanPropertyT_range_of_injective (#audit_axioms) takes the printed hypotheses that S is finitely "
     "generated and phi injective; owners ct-bilateral-mf, ct-bilateral-cell"),
    (lambda d, det, dt: re.search(r"\.ChainCore\.DynamicRankBudget\.(PrintedDynamicRankBudget"
                                  r"|printedDynamicRankBudget_of_(pieces|residuals)|PrintedIntroductionAperiodicSentence"
                                  r"|printedIntroductionAperiodicSentence_of_budget)$", d),
     "cor:dynamic-rank-budget and the Introduction's aperiodic sentence (tex 254-259), a scaffold (rows 87a9e0862, "
     "0968ba9c3; DynamicRankBudget at a2cb17f58 and DynamicRankBudgetTorsionTransfer at aadb514ad, neither root-imported "
     "at 4af014f74): PrintedDynamicRankBudget and PrintedIntroductionAperiodicSentence are named Props of the printed "
     "statements, proved by printedDynamicRankBudget_of_pieces, printedDynamicRankBudget_of_residuals and "
     "printedIntroductionAperiodicSentence_of_budget (#audit_axioms) only from piece Props that nothing produces yet, "
     "open residuals, not citations: CoreRingReflectionStatement (chain-reflection), CoreModelsLEFStatement "
     "(chain-itinerary), CountableCrossedProductStatement (chain-core), CoreMFRadicalKillStatement (chain-radical), "
     "BilateralThreeTransferStatement (ct-bilateral-mf), UnitKernelLocallyFiniteStatement (ct-involution) and "
     "ReturnEmbeddingStatement (ct-return-tower, ct-rank-budget, ct-involution); the eighth piece, "
     "TorsionDefectTransferStatement, is proved over CountableCrossedProductStatement by "
     "torsionDefectTransferStatement_of_countable (#audit_axioms) from the closed "
     "manuscriptTorsionComplementaryIdempotents; owner ct-rank-budget"),
    (lambda d, det, dt: det == "inlined-statement" and re.search(
        r"\.(manuscriptSentence_hullGeneratingSetLimitSet|manuscriptSaturationLimitSet_of_leastAreaLeaves)$", d),
     HHARD_WHY),
    (lambda d, det, dt: re.search(r"\.(ChainRespellInput|CornerInsertionInput|PendantPathRemovalInput"
                                  r"|SeparatingPathRemovalInput|chainRespellInput_of_pieces"
                                  r"|separatingPathRemovalInput_of_pendant)$", d),
     "Osin Lemma 9.4 Case 2, the respelling of a cutting chain (\"This contradicts our assumption that the sum of "
     "l(t_i) " + CHAIN_HEAD + " (#audit_axioms, OsinLemma94ChainRespell, 7a225d1d0) "
     "proves ChainRespellInput from CornerInsertionInput and SeparatingPathRemovalInput, and "
     "separatingPathRemovalInput_of_pendant (#audit_axioms, OsinLemma94SeparatingRemoval, 7d4a2515f) proves "
     "SeparatingPathRemovalInput from PendantPathRemovalInput by a G-face merge across the first edge; "
     + CHAIN_PRODUCED + "the buried premises (S.RunsBackAcross, "
     "S.DegreeTwoJoints, S.UnselectedGFace) are hypotheses inside these Props, which each consumer supplies; the "
     "consumer is OsinLemma94CuttingChainsInput (OsinLemma94PolygonRealization, 1130c8dbc); " + REACH_CHAIN + "; owners "
     "hull-unbound, simple-group (CornerInsertionInput), jacobson (PendantPathRemovalInput)"),
    (lambda d, det, dt: det == "open-predicate" and d.endswith(".osinLemma94PolygonCoversInput"),
     "Osin Lemma 9.4, the covering half of the count, open: osinLemma94PolygonCoversInput (#audit_axioms, "
     "OsinLemma94PolygonCount, 2b2e16cc6, root-imported) gives S <= sum S_i + L n with L = 24 eps over the premise "
     "hsame : OsinLemma94UnboundSameCellStatement (no unbound dart has its own cell across), added at f04929ebb; it is an "
     "open residual that nothing produces yet, consumed by osinLemma94PolygonCountInput_of_sideBudget and "
     "OsinGreendlingerOpenResiduals (lead ruling 09-13 16:00); owner hull-count94 (class route, with ghw-charp2's "
     "respell)"),
    (lambda d, det, dt: re.search(r"\.(OsinLemma94PolygonSideBudgetInput|osinLemma94PolygonCountInput_of_sideBudget)$", d),
     "Osin Lemma 9.4 count piece, open: osinLemma94PolygonCountInput_of_sideBudget (#audit_axioms, "
     "OsinLemma94PolygonCount, 2b2e16cc6) proves OsinLemma94PolygonCountInput from OsinLemma94PolygonSideBudgetInput "
     "(Lemma 9.3 \"sum n_i <= 53 n\" and (38) \"k_i <= 4 n_i\": the maximal polygons of a dart-minimal optimum have at "
     "most K n sides) " + COVERS + "; " + SIDE_BUDGET_OPEN + "; " + REACH_COUNT + COUNT_OWNER),
    (lambda d, det, dt: re.search(r"\.(osinLemma94PolygonRealizationInput_of_pieces|OsinLemma94CuttingChainsInput"
                                  r"|OsinLemma94CellArcsInput|OsinLemma94BoundaryArcsInput|OsinLemma94PolygonPartitionInput"
                                  r"|QuasiGeodesicRespellInput|GFacesApart|CellArcsQuasiGeodesic|BoundaryArcsQuasiGeodesic"
                                  r"|CuttingChainsQuasiGeodesic|gFacesApart_of_dartMinimal"
                                  r"|osinLemma94PolygonRealizationInput_of_partition|osinLemma94PolygonRealizationInput"
                                  r"|osinLemma94PolygonPartitionInput|osinLemma94CellArcsInput_holds"
                                  r"|osinLemma94BoundaryArcsInput)$", d),
     "Osin Lemma 9.4, the realization of the component polygons (each component is cut \"along t_1, ..., t_l\" into a "
     + REAL_HEAD + " (#audit_axioms, OsinLemma94PolygonRealization, "
     "1130c8dbc; eps0 = rho0 = 1) proves OsinLemma94PolygonRealizationInput " + REAL_SOME + CUTTING + ", " + CELL + ", "
     + BOUNDARY + " and " + PARTITION + "; gFacesApart_of_dartMinimal (#audit_axioms) proves that two different "
     "unselected G-faces share no "
     "edge under S.DartMinimal, the fewest-darts hypothesis that exists_reduced_dartMinimal supplies (#audit_axioms, "
     "OsinLemma94DartMinimal, b6bda9923), since a G-face merge removes two darts and keeps the unbound sum; GFacesApart "
     "and the three QuasiGeodesic predicates are the hypotheses of the partition piece; " + REACH_REAL + "; owners "
     "hull-unbound, ghw-assembly"),
    (lambda d, det, dt: re.search(r"\.(osinLemma94CuttingChainsInput_of_pieces|quasiGeodesicRespellInput|chain_rel_getElem"
                                  r"|facePerm_getElem_of_rotate_eq|listVal_drop_take_eq_vertex|not_leaf_of_dartMinimal"
                                  r"|alpha_not_mem_of_dartMinimal)$", d),
     "Osin Lemma 9.4, the cutting chains with the fewest darts are (lambda, c + 2)-quasi-geodesic: "
     "osinLemma94CuttingChainsInput_of_pieces (#audit_axioms, OsinLemma94CuttingChains, 26b30e5df, 108236c25) derives "
     "OsinLemma94CuttingChainsInput from ChainRespellInput, PendantPathRemovalInput and QuasiGeodesicRespellInput, all "
     "produced: " + CHAIN_PRODUCED + "QuasiGeodesicRespellInput is produced by quasiGeodesicRespellInput (#audit_axioms, "
     "OsinLemma94QuasiGeodesicRespell, bbb8585ab); chain_rel_getElem (an IsChain list relates consecutive entries) and "
     "facePerm_getElem_of_rotate_eq (consecutive darts of a rotated face walk follow the face permutation) are lemmas "
     "whose hypotheses, the IsChain premise, the index bound and the rotation equation hwalk, each caller holds, and "
     "listVal_drop_take_eq_vertex is an identity with no hypotheses; not_leaf_of_dartMinimal refutes a leaf (hd, hleaf) "
     "inside an unselected G-face, and alpha_not_mem_of_dartMinimal shows that a chain read off such a face (hwalk) that "
     "runs back across (hjoints) contains no reversed dart, both from hpendant : PendantPathRemovalInput, "
     "hS : S.DartMinimal and hf : S.UnselectedGFace f, which each consumer holds, since PendantPathRemovalInput is "
     "produced and exists_reduced_dartMinimal (#audit_axioms, OsinLemma94DartMinimal, b6bda9923) supplies DartMinimal; "
     + ROOTED_PIECES + "; owners hull-unbound, simple-group, jacobson"),
    (lambda d, det, dt: re.search(r"\.(osinLemma94CaseTwoInput|osinLemma94CaseTwoInput_of_insertion|osinLemma94CaseTwo_false"
                                  r"|SeparatedCornerInsertionInput|separatedCornerInsertionInput)$", d),
     "Osin Lemma 9.4 Case 2 (\"This contradicts our assumption that the sum of l(t_i) is minimal\") is closed: "
     "osinLemma94CaseTwoInput (#audit_closed_axioms, OsinLemma94CaseTwo, e0e94015d) applies "
     "osinLemma94CaseTwoInput_of_insertion (#audit_axioms, 52b77f408) to separatedCornerInsertionInput "
     "(#audit_closed_axioms, OsinLemma94SeparatedInsertionProof, 619b70139), which proves SeparatedCornerInsertionInput "
     "(OsinLemma94SeparatedInsertion); osinLemma94CaseTwo_false (#audit_axioms) refutes one backwards connector pair onto "
     "a cutting side from hinsert, 3 <= eps and hS : S.DartMinimal, and its other hypotheses (the realized polygons P, "
     "the polygon k, the pair C, hback, hcut) are the configuration it refutes, over which "
     "osinLemma94CaseTwoInput_of_insertion quantifies; OsinLemma94CaseTwo, OsinLemma94SeparatedInsertion and "
     "OsinLemma94SeparatedInsertionProof are "
     "root-imported at " + ROOTED_AT + "; owners sec5-sentences, sec2-sentences"),
    (lambda d, det, dt: re.search(r"\.osinLemma94Section_of_residuals$", d),
     "Osin's Lemma 9.4 over its two residual pieces inside the least-area Hull 7.1 route: "
     "osinLemma94Section_of_residuals (#audit_axioms, OsinLemma94SectionResiduals, 0087a5095, 409bbbf72, 4002b9371) "
     "applies osinLemma94Section_of_planarPieces (#audit_axioms, 80790fad1) to the closed metric half "
     "osinLemma94AntiparallelMetric (#audit_closed_axioms, e3da1ba60), the closed realization "
     "osinLemma94PolygonRealizationInput (#audit_closed_axioms, 4002b9371) and the closed Case 2 osinLemma94CaseTwoInput "
     "(#audit_closed_axioms, e0e94015d); its hypotheses are hcount, " + COUNT_PIECE + ", and hone, " + CASE_ONE + "; "
     + ROOTED_PIECES + "; owners hull-unbound, sec5-sentences, hull-count94, theoremc-retire"),
    (lambda d, det, dt: re.search(r"\.(isHyperbolicallyEmbedded_transitiveRelGenSet|exists_guessingData_transitive"
                                  r"|printedHullLemma35|PrintedHullLemma35)$", d),
     "Hull's Lemma 3.5 at its printed generality (\"Suppose {H_i} ->h G, and for each i, {K^i_j} ->h H_i. Then "
     "{K^i_j} ->h G\"): the premises that the families are hyperbolically embedded are the printed hypotheses of the "
     "lemma, not citations, and printedHullLemma35 (#audit_closed_axioms, HullLemma35Closed, b5f91627e) proves "
     "PrintedHullLemma35 (HullLemma35Printed, dd0412114) from them; HullLemma35Printed and HullLemma35Closed are "
     "root-imported at " + ROOTED_AT + "; owner baseline-debt"),
    (lambda d, det, dt: d.endswith("KotowskiOllivierClosed.kotowskiOllivier_of_pinched"),
     "an intermediate step of the closed hKO chain: hpinch (Systolic.MirrorFoldPinchedStatement on CCKW.cosetComplex) is "
     "produced by Systolic.mirrorFoldPinched (426813b24), and KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed "
     "applies it (#audit_closed_axioms, root-imported, f65f99f17); owner ko-closed"),
    (lambda d, det, dt: "KotowskiOllivierClosed" in d, HKO_CHAIN_WHY),
    (lambda d, det, dt: re.search(r"ZipSpurStatement|ZipPinchStatement|MirrorFoldStatement"
                                  r"|SystolicInvariantCliqueStatement", dt),
     HKO_WHY),
    (lambda d, det, dt: d.endswith("LeavittMFQuotientBothInclusions.elementary_le_commutator_of_trivial"),
     "premise \"every homomorphism from EL_d(R) to an MF group is trivial\" is thm:full-defect-ring at R = L_k(1,d), "
     "proved unconditionally by FullDefectRingEJZUnconditional.manuscriptLeavittAlgebraFullDefectRankTwoAllCharacteristics "
     "inside the sibling carrier manuscriptSentence_bothInclusionsPrinted, cited in the same census row; the printed "
     "implication as internal proof modularization, not an external citation; owner leavitt-units"),
    (lambda d, det, dt: d.endswith("HullTheorem312Lemma58.normalizesNoNontrivialFinite_of_isHyperbolicallyEmbedded"),
     "premise D.IsHyperbolicallyEmbedded is the definition (DGO Definition 4.25: hyperbolic relative Cayley graph, "
     "locally finite relative metrics) inside Hull Lemma 5.8's printed hypothesis that <h> is hyperbolically embedded "
     "in (G,X); the sibling carrier printedHullLemma58, cited in the same census row, takes it from that printed "
     "hypothesis; not a citation; owner cite-hull"),
    (lambda d, det, dt: "FullDefectCornerRemark.manuscriptSentence_cornerPassesUp" in d,
     "the premise FullDefectPair (Corner R p hp) is the printed hypothesis of the sentence itself (\"if the ring pRp, "
     "with unit p, satisfies the hypothesis\"), carried exactly as printed; not a citation"),
    (lambda d, det, dt: "powersAveragingEstimate_of_naiveFreeProductProperty" in d,
     "an intermediate lemma cited beside the closed endpoint dgoTheorem235Printed; NaiveFreeProductProperty G is the "
     "group property NaiveFreeProductAtAcylindricallyHyperbolicProof establishes at acylindrically hyperbolic groups; "
     "owners dgo-analytic, dgo-geometric, go-sr1"),
    (lambda d, det, dt: "KotowskiOllivierStatement" in dt, G0_WHY),
    (lambda d, det, dt: re.search(r"HydeLodha\.(finitelyPresentedInfiniteSimpleStatement_of_(dynamics|upsilon|stabK)"
                                  r"|upsilonFinitelyPresented_of_dynamics|lemmaFourSixCaseOne_of_dynamics"
                                  r"|stabKFinitelyPresented_of_upsilon)$", d),
     "an intermediate step of the closed hW chain (Hyde-Lodha Lemma 4.6, Proposition 4.7, Theorem 4.8), cited beside "
     "the closed endpoint HydeLodha.finitelyPresentedInfiniteSimple_closed, which discharges every premise of the chain "
     "with HydeLodha.lemmaFourSixDynamics (both #audit_closed_axioms); owner simple-group"),
    (lambda d, det, dt: "FinitelyPresentedInfiniteSimpleStatement" in dt,
     "FFF S2 needs a finitely presented torsion-free infinite simple group (FinitelyPresentedInfiniteSimpleStatement, "
     "Hyde-Lodha), closed as HydeLodha.finitelyPresentedInfiniteSimple_closed; owner simple-group"),
    (lambda d, det, dt: re.search(r"FournierFacioParagraph|LiteratureInputs", dt) or d.endswith("FournierFacioParagraph"),
     "the Fournier-Facio paragraph (FFF S2) is produced only over the walls of sec:torsion-free; " + WALLS + "; "
     + GREEN_OWNERS),
    (lambda d, det, dt: re.search(r"EstimatingUnboundOutputStatement|RelativeIsoperimetricBridgeQuasiGeodesicStatement\."
                                  r"|RelativeGreendlingerQuasiGeodesicStatement\.", dt),
     "the historical quasi-geodesic leaves of Hull Theorem 7.1 (EstimatingUnboundOutputStatement is refuted on main, and "
     "no producer exists for the old bridge), cited beside the least-area route that replaces them; owners hull-select, "
     "hull-unbound, hull-bridge, hull-respell, sec5-sentences"),
    (lambda d, det, dt: re.search(r"RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement"
                                  r"|RelativeGreendlingerQuasiGeodesicLeastAreaStatement|QuotientPeripheralLetterPullback", dt),
     LEAST_AREA_WHY),
    (lambda d, det, dt: det.startswith("carrier-") and d.endswith("HullCorollary74.PrintedHullCorollary74"),
     COR74_CARRIER_WHY),
    (lambda d, det, dt: d.endswith("HullCorollary74.exists_commonQuotient_of_hullGeneratingSet")
     and not re.search(r"HullTower", dt),
     COR74_HYP_WHY),
    (lambda d, det, dt: re.search(r"BoundedImageEmbeddingStatement|BoundedHullLemma44CanonicalQuotientStatement"
                                  r"|HullLemma44CanonicalQuotientStatement|HullOneStepStatement|HullTower", dt),
     L44_WHY),
    (lambda d, det, dt: d.endswith("VanKampen.OsinLemma94PlanarPolygons.unbound_lt"),
     "the buried premise hmetric is OsinLemma94DensePolygonsAntiparallel at fixed parameters, the instance of "
     "OsinLemma94AntiparallelMetricStatement (closed by osinLemma94AntiparallelMetric, #audit_closed_axioms, e3da1ba60) "
     "that osinLemma94Section_of_pieces supplies at every threshold; the row's residual is OsinLemma94PlanarRunInput "
     "alone; owners hull-unbound, sec5-sentences"),
    (lambda d, det, dt: re.search(r"osinLemma94Section_of_planarPieces|OsinLemma94PolygonRealizationInput"
                                  r"|OsinLemma94PolygonCountInput|OsinLemma94CaseOneInput|OsinLemma94CaseTwoInput"
                                  r"|OsinLemma94RealizedPolygons|GloballyDistinguishedSectionFamily\.DartMinimal"
                                  r"|exists_dartMinimal|exists_reduced_dartMinimal", d + " " + dt),
     PLANAR_PIECES_WHY),
    (lambda d, det, dt: re.search(r"OsinLemma94PlanarRunInput|osinLemma94Section_of_pieces|OsinLemma94PlanarPolygons"
                                  r"|OsinLemma94AntiparallelMetricStatement|OsinLemma94DensePolygonsAntiparallel",
                                  d + " " + dt),
     PIECES_WHY),
    (lambda d, det, dt: d.endswith("VanKampen.OsinLemma94ComponentPolygons.unbound_lt"),
     "the buried premise hmetric is the metric conclusion of UnboundEstimate.unboundComponentWordPolygonsMonotone (Osin "
     "Lemma 3.7 on the component polygons, #audit_closed_axioms, root-imported), which osinLemma94Section_of_runInput "
     "supplies at every threshold; this run-input route is superseded by osinLemma94Section_of_pieces, whose only "
     "residual is OsinLemma94PlanarRunInput; owners hull-unbound, sec5-sentences"),
    (lambda d, det, dt: re.search(r"OsinLemma94RunInput", d + " " + dt),
     "Osin's Lemma 9.4 run input (OsinLemma94RunInput), superseded: its no_connector forbids connector pairs in both "
     "orientations, more than Osin's Cases 1 and 2 prove, and no RunProducer module will be built; the least-area Hull "
     "7.1 route runs through osinLemma94Section_of_pieces, whose only residual is OsinLemma94PlanarRunInput; owners "
     "hull-unbound, sec5-sentences"),
    (lambda d, det, dt: det.startswith("carrier-") and re.search(r"TorsionFree|HullSmallCancellation|RegularNonMFAlgebra"
                                                                 r"|Saturation", d),
     CARRIER_WHY),
]

# Census successor (lane ms-cite-2, 2026-09-13 18:55): the open named residuals of the sec:chain-core tail
# assemblies (ct-*, ms-* lanes).  A finding is registered here only when its declaration lives in the ChainCore or
# ClopenCrossedProduct namespace, the verifier says what it waits on is a named Prop nothing produces yet, and EVERY
# row citing it is graded partial or open in the census this merge just wrote (cwd metadata/).  A finding on a
# formalized or definition row stays UNCLASSIFIED, so the gate stays red.
def _census_status():
    st = {}
    try:
        for raw in open("metadata/NON_MF_SENTENCE_CENSUS.tsv", encoding="utf-8"):
            if raw.startswith("#") or raw.startswith("key\t"):
                continue
            p = raw.rstrip("\n").split("\t")
            if len(p) >= 6:
                st[p[0]] = p[5]
    except OSError:
        pass
    return st


CENSUS_STATUS = _census_status()
CHAIN_TAIL_OWNERS = [
    ("RankTwo", "ct-rank-two-limit, with chain-matricial for the kernel piece"),
    ("DynamicRankBudget", "ct-rank-budget, with ct-return-tower and ct-involution"),
    ("CoreMFRadicalGLKill", "ms-core-5, with ct-bilateral-mf for PrintedBilateralThree"),
    ("InvolutionLocalization", "ct-involution, ms-core-3"),
    ("_of_matricial", "ms-units, with chain-matricial for TransientIdealLocallyMatricialFTwoStatement"),
    ("TransientIdealLocallyMatricial", "chain-matricial, with second starts ms-units and ms-core-4"),
    ("BilateralThree", "ct-bilateral-mf"),
]


def chain_tail_why(decl, det, detail, rows):
    if not re.match(r"GroupApproximation\.(ChainCore|ClopenCrossedProduct)\.", decl):
        return None
    if det not in ("carrier-data", "open-predicate", "buried-conditional"):
        return None
    if "nothing in the corpus ever produces" not in detail and "has head" not in detail:
        return None
    if not rows or any(CENSUS_STATUS.get(r) not in ("partial", "open") for r in rows):
        return None
    premises = sorted(set(re.findall(r"premise `([^`]+)`", detail)))
    what = ("the premise(s) " + ", ".join(premises)) if premises else ("the named Prop " + decl.split(".")[-1])
    owners = next((o for key, o in CHAIN_TAIL_OWNERS if key in decl), "the landing lane of the module "
                  "(notes/nm-swarm/WORKLIST.md)")
    return ("open residual of the sec:chain-core tail, not a citation: " + decl.split(".")[-1] + " waits on " + what
            + ", which nothing produces at this merge; every row citing it (" + " ".join(rows) + ") is graded "
            "partial, and the line goes the day a closed producer lands; owners " + owners
            + " (census successor ms-cite-2, 2026-09-13)")


added, unclassified = [], []
for (det, decl), rec in new.items():
    if (det, decl) in registered:
        continue
    why = next((w for test, w in RULES if test(decl, det, rec["detail"])), None)
    if why is None:
        why = chain_tail_why(decl, det, rec["detail"], rec["rows"])
    if why is None:
        unclassified.append("%s %s rows %s: %s" % (det, decl, " ".join(rec["rows"]), rec["detail"][:300]))
        continue
    added.append("%s %s  -- rows %s (census merge %s): %s" % (det, decl, " ".join(rec["rows"]), sha9, why))

if added:
    out.append("#")
    out.append("# Added by the census merge at %s (lane census, non-MF every-line swarm 2026-09-13): every line sits "
               "on a row graded partial, except a printed hypothesis or a finding the line calls not a conditional; a "
               "line goes the day its premise gets a closed producer or its row stops naming the declaration." % sha9)
    out.extend(added)
with open(base_out, "w", encoding="utf-8") as fh:
    fh.write("\n".join(out) + "\n")
print("register", sha9, "stale removed", len(stale), "revised", revised, "new registered", len(added),
      "unclassified", len(unclassified))
for u in unclassified:
    print("UNCLASSIFIED", u)
sys.exit(3 if unclassified else 0)
