# ko-closed — the Kotowski–Ollivier input `hKO` from `GHB(7)` (lane ko-closed, clone thm-e, 2026-09-13)

Predecessor: kh-hyperbolic (dead; report `kh-hyperbolic.md`).  Target: `Kazhdan/KotowskiOllivierClosed.lean`,
closed `kotowskiOllivier_closed : TheoremC.KotowskiOllivierStatement`.

## STATE (09-13 ~10:00): `OsinLemma94CaseOneWalkStatement` PROVED (theoremc-retire's walk sub-piece)
`theorem GroupApproximation.GGT.VanKampen.osinLemma94CaseOneWalk : OsinLemma94CaseOneWalkStatement.{u, w, v}` is in
`GGT/VanKampen/Estimating/OsinLemma94CaseOneWalkHolds.lean`.  The list and arc facts are in
`OsinLemma94CaseOneWalkLists.lean`.
- The statement is unchanged: theoremc-retire's fd6ce3c09, md5 6038689296f15b2d6c53c5ea0fe70625.  Every conjunct is true
  as stated, so no counter-shape was sent.
- No binder, sorry or axiom, with `#audit_axioms` in both modules.
- LANDED:
  - eb9010962: both modules, unverified;
  - 8f0f73966: the linter fix.
- Probe 0913-094857-38535 built Lists green and stopped Holds at one linter error, `exact hkt` after `rfl`.
- Probe 0913-095509-55850 (base c99e3bec1) built Holds GREEN.
  - `osinLemma94CaseOneWalk` depends on propext, Classical.choice and Quot.sound.
  - Wire-queued: Lists at eb9010962, Holds at 8f0f73966.
- A grep for `9\.4` in the tex finds nothing, so this piece has no census row of its own.  Its consumer is theoremc-retire's
  `OsinLemma94CaseOneInput`.
- The proof:
  1. The walk of polygon `k`, rotated to `base k`, is the concatenation of the sides.  So `[a, a']` and `[b', b]` are windows
     at the block starts (`rangeFlatMap_split`, `rangeFlatMap_drop_take`).
  2. Rotating to `a'` reads `X ++ T ++ Y ++ P` (`rotate_four_inside` or `rotate_four_wrap`, depending on which side comes
     first).
  3. Corners are prefix values and the whole walk has value 1 (`polygon_vertex_eq`, `walk_four_windows`), which gives the
     values of `X` and `Y`.
  4. `P` and `T` are sub-arcs of the arcs from `cell_arc` and `boundary_arc` (`cyclicArc_exists_sub`,
     `cyclicArc_exists_sub_reverse`).  An `∂Δ` arc inside section `j` ends by `cut (j+1) ≤ |∂Δ|`, so its sub-arc does
     not wrap and stays inside the section.
- Residual Props owned by ko-closed: NONE.

## STATE (09-13 ~07:20): hKO and SharpExistence CLOSED; flip item withdrawn (hull-bridge)
`theorem GroupApproximation.KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed :
Manuscript.NonMF.TheoremC.KotowskiOllivierStatement :=
kotowskiOllivier_of_pinched (Systolic.mirrorFoldPinched CCKW.cosetComplex)`, and
`theorem GroupApproximation.Hyperbolic.sharpExistence_closed : SharpExistence := kotowskiOllivier_closed`.
- Neither endpoint has a binder.  `#audit_closed_axioms` passes on both with propext, Classical.choice and Quot.sound.
- `sharpExistence_closed` LANDED b0ab67b4a after probe 0913-065114-20727 (base c48f20f41) went green.  Wire-queued at
  b0ab67b4a (the module is root-reachable).  `kotowskiOllivier_closed` LANDED f65f99f17.
- Every leaf is closed:
  - hzip is `CCKW.zipSpur_cosetComplex` (`GGT/SystolicDiscZip.lean`, 8389a0e6c, kh-torsion);
  - Distinct is `Systolic.mirrorFoldDistinct` (81b06b43e, ko-closed);
  - Pinched is `Systolic.mirrorFoldPinched` (`GGT/SystolicDiscMirrorFold.lean`, 426813b24, fff-periodic).

  hT6 is not needed: `sharpExistence_ghb7_of_zipFoldHyp`.
- Residual Props owned by ko-closed: NONE.

## ASSIGNMENT (lead, 09-13 ~06:50)
1. `Hyperbolic.SharpExistence` with no binder: DONE, `Hyperbolic.sharpExistence_closed` (b0ab67b4a).
2. WITHDRAWN by the lead (~07:15).  hull-bridge owns the flips for nm-endpoints' five endpoint modules: it has unlanded
   drafts `TorsionFreeGreendlingerForms.lean` and `TorsionFreeGreendlingerSentences.lean`, and the roster's
   "Reassignments 09-13 ~06:30" gives it those modules.  ko-closed wrote nothing for them.  Before the withdrawal,
   ko-closed found and sent nm-endpoints and census the following (the mapping is in this report at 62e77b1cf):
   - fff-periodic's `TorsionFreeGreendlingerLeaf` (1edf0f7b4) already has forms that take `hgreendlinger` alone;
   - the 18 old declarations are named only in sec5-sentences' rows LINE:284, 291, 1636, 1650 and 1718;
   - `TorsionFreeGreendlingerLeaf` is imported by nothing.  I reported it as missing from the wire queue, but that was
     wrong: my grep was cut off at five matches.  It is queued at line 501 (fff-periodic, 06:45).
3. Row 8097c371f35d is nm-endpoints' file (`metadata/nm-census-rows/nm-endpoints.tsv`); do not land it.  Its carriers are
   the `TorsionFreeFourLeaves` forms.  Baseline lines 369-370 (`kotowskiOllivier_of_leaves`, open-predicate and
   buried-conditional, census merge 63f147d7b) came from ko-closed's old LINE:1675 row, which dropped that carrier at
   2d25ebab5.  Row LINE:1675 now names `kotowskiOllivier_closed` and `Hyperbolic.sharpExistence_closed`, and drops
   `kotowskiOllivier_of_pinched`, which has a binder.  I sent both `_closed` names to nm-endpoints, who swaps and
   re-grades their own row, and asked census to retire the two lines at its next merge.

## LANDED (all GREEN, all wire-queued)
| module | SHA | probe |
|---|---|---|
| `Kazhdan/KotowskiOllivierClosed` (`kotowskiOllivier_of_leaves`) | c5a8ae8fb | 0913-011617-71747 |
| `GGT/SystolicDiscMirrorFoldCases` (Distinct/Pinched Props, `mirrorFoldStatement_of_cases`, `faceOf_alpha_ne_of_inner`) | 0fb6f2305 | green |
| `GGT/SystolicDiscMirrorFoldSteps` (`digonBack`, `CycleDisc.exists_of_embed`) | 79b8c51c8 | green |
| `GGT/SystolicDiscMirrorFoldQuad` (`MirrorQuad`, three moves, `planar3`, `faceCount_add_two`) | b110363ae | 0913-041349-71786 |
| `GGT/SystolicDiscMirrorFoldEmbed` (`tau`, `tau_facePerm`, `tau_injective`, `tau_cases`, `exists_tau_eq_of_ne`) | 781dcb8bf | 0913-042826-7309 |
| `GGT/SystolicDiscMirrorFoldDistinct` (`mirrorFoldDistinct`) | 81b06b43e | 0913-044647-45237 |
| `Kazhdan/KotowskiOllivierClosed` (`kotowskiOllivier_of_pinched`, the one-leaf reduction) | cf1675f3b | 0913-045023-55941 |
| `Kazhdan/KotowskiOllivierClosed` (docstring: the `hKO` binders after 2c3c8cb40, reported by sec2-sentences) | 4be3a3a5c | 0913-052526-4611 |
| `Kazhdan/KotowskiOllivierClosed` (`kotowskiOllivier_closed`; imports `GGT/SystolicDiscMirrorFold`) | f65f99f17 | 0913-055250-45566 |
| `Kazhdan/KotowskiOllivierClosed` (`Hyperbolic.sharpExistence_closed`) | b0ab67b4a | 0913-065114-20727 |

Census row LINE:1675 (`kotowskiOllivier_closed`, `Hyperbolic.sharpExistence_closed`, partial).  It closes the `hKO`
input only, and the rest of the sentence belongs to other rows.

`theorem mirrorFoldDistinct (X : TriangleComplex V) : MirrorFoldDistinctStatement X`.  `#print axioms` gives propext,
Classical.choice and Quot.sound.  dgo-geometric independently audited the Prop as true.

## hfold SPLIT (Option A, agreed with fff-periodic)
Setup: `d : a→b` in the inner face `[d, d1, d2]`, `alpha d` in `[alpha d, e1, e2]`, and the third corners carry one label.
- DISTINCT (ko-closed, CLOSED), in three moves:
  1. Delete the edge of `d`, which leaves a square.
  2. Fold `d2` onto `alpha e1` (`FoldMap.IsFoldable`: the two ends differ).
  3. Delete the digon edge `e2''`.

  The final map embeds in the disc by `tau` along face rotation, reads labels compatibly and covers the exterior
  cycle.  So it is a cycle disc with the same boundary and two faces fewer.
- PINCHED (fff-periodic, CLOSED): edge deletion, vertex split, restriction to the outer component, digon deletion
  (`FoldStage.exists_disc_of_pinch`, 08ae1c587).
- The final composition `Systolic.mirrorFold (X) : MirrorFoldStatement X` landed in fff-periodic's
  `GGT/SystolicDiscMirrorFold.lean` (426813b24).  My draft of the same composition is dropped, and nothing was landed at that path.

## ORPHANS
`Kazhdan/KotowskiOllivierLeaves.lean` → ko-closed.  VERDICT (accepted by the lead): leave it; no deletion.  Nothing on main
imports it.

## COORDINATION
- theoremc-retire (~06:00):
  - flip `hKO := KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed` in the `_of_leastAreaInputs` forms and
    `SeedFromTheoremC`, once `Kazhdan.KotowskiOllivierClosed` is wired;
  - also, `hfold := Systolic.mirrorFold CCKW.cosetComplex` for the `_of_leastAreaZipFold` forms.
- nm-endpoints (~06:00): the rows that waited on `hpinch` now wait on wall 1 only.
  - ~07:10: I proposed a split for item 2.
  - ~07:15: they replied that no split is needed and hull-bridge owns the flips.  Row 8097c371f35d is in their tsv,
    and they swap its carrier themselves.  I sent them `kotowskiOllivier_closed` and `Hyperbolic.sharpExistence_closed`.
- census (~07:10): asked to retire baseline lines 369-370.  (~07:15): told that no five-module mapping will come.
- main (~07:10): milestone report, plus the unwired `TorsionFreeGreendlingerLeaf`.
- kh-cckw: the every-X HC6 is `Systolic.mirrorFold`.  This corrects my earlier name `mirrorFoldStatement`.
- sec2-sentences: docstring fixed (4be3a3a5c).

## NEXT (lead, 09-13 ~07:25; restated after the ~08:30 restart): help theoremc-retire with `OsinLemma94CaseOneInput`
The Prop is in hull-unbound's `GGT/VanKampen/Estimating/OsinLemma94PlanarPieces.lean` (80790fad1).  theoremc-retire
landed the face-walk piece `OsinLemma94CaseOneWalkStatement` (`Estimating/OsinLemma94CaseOneWalk.lean`, 8a36ad06c).
theoremc-retire assigned ko-closed the walk piece.  It is proved, as recorded in STATE above.  theoremc-retire owns pieces
(a)-(d) below.

Findings sent to theoremc-retire and main.  Two gaps separate CaseOneWalk from
`RealizedSectionFamily.false_of_quadrilateral_region`:
- (B1) `NoInternalFaceDart` for `P.face k` is false when polygon `k` has a cutting side, because `cutting_internal` puts
  both sides of the path in face `k`.  So `FaceSetBoundary.ofSingleton`, and with it the singleton `InnerGRegion`, is
  unavailable.  But `GFaceWordInsertion.exists_quadrilateral_region` uses `hno` only in `hold_face`
  (`GFaceQuadrilateralRegion.lean:255-262`), applied at :280 to darts of the source arc `P` and at :290 to darts of the
  target arc `T`.  For those darts `faceOf (alpha z) ≠ f` follows from `hcells` and `hf`.
- (B2) CaseOneWalk gives `darts.rotate r`, while the surgery needs `r = 0`.  `faceBoundary` is a `DiscDiagram` field
  (`DiscDiagram.lean:111`), but re-basing it does not carry `S` by `rfl`.

Proposed pieces:
- (a) a rotated, `hno`-free `exists_quadrilateral_region`;
- (b) `false_of_quadrilateral_face` on `S.diagram` directly;
- (c) connector glue: `s1 := endConnector`, `s2 := startConnector`, an empty connector padded to `[l, inv l]` with `l`
  a label on `P`, and `eps0 ≥ 2`;
- (d) the assembly `OsinLemma94CaseOneInput`.

nm-endpoints swaps the carrier on its row 8097c371f35d, and census retires baseline lines 369-370 at its next merge.
