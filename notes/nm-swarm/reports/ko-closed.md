# ko-closed — the Kotowski–Ollivier input `hKO` from `GHB(7)` (lane ko-closed, clone thm-e, 2026-09-13)

Predecessor: kh-hyperbolic (dead; report `kh-hyperbolic.md`).  Target: `Kazhdan/KotowskiOllivierClosed.lean`,
closed `kotowskiOllivier_closed : TheoremC.KotowskiOllivierStatement`.

## STATE (09-13 ~07:10): hKO and SharpExistence CLOSED; flip item in coordination
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
2. Flips for nm-endpoints' five modules (27 baseline findings).  Finding: no new module is needed.
   fff-periodic's `Manuscript/NonMF/TorsionFreeGreendlingerLeaf.lean` (1edf0f7b4, probe 0913-063820-983 green) already
   has a form that takes `hgreendlinger` alone for each of them, and fff-periodic's rows name those forms on the same
   hashes.  The only rows that still name the 18 old declarations are sec5-sentences' LINE:284, 291, 1636, 1650 and 1718.
   So each flip is a carrier drop in those rows.  The split was proposed to nm-endpoints, and the mapping goes to census once they agree.
   Old → new (`TorsionFreeGreendlingerLeaf.*`):
   - LeastAreaAssembly `manuscriptTorsionFreeTheorem_of_leastAreaLeaves` → `printedTorsionFreeTheorem_of_greendlinger`;
     `printedSaturationNoOmega_of_leastAreaLeaves` → `printedSaturation_of_greendlinger`;
     `manuscriptRegularNonMFAlgebra_of_leastAreaLeaves` → `printedRegularNonMFAlgebra_of_greendlinger`.
   - OsinNotion `manuscript{TorsionFreeTheorem,Saturation,RegularNonMFAlgebra}Osin_of_leastAreaLeaves` →
     `printed{TorsionFreeTheorem,Saturation,RegularNonMFAlgebra}Osin_of_greendlinger`.  The 3 carrier-data lines
     (`Printed*Osin`) wait for W1.
   - HullPrintedLeastArea `manuscriptSentence_hullTheorem{,Osin}_of_leastAreaLeaves` → `printedHullTheorem{,Osin}_of_greendlinger`.
   - LimitSetEndpoints `manuscript{HullTheorem,Saturation}LimitSet_of_leastAreaLeaves` →
     `printed{HullTheorem,Saturation}LimitSet_of_greendlinger`.
   - SectionAssembly `manuscriptRegularNonMFAlgebra{,Osin,LimitSet}_of_hullLeaves_closedGO` and
     `manuscriptRegularNonMFAlgebra_closedCitations` → `printedRegularNonMFAlgebra{,Osin,LimitSet}_of_greendlinger`.
3. Row 8097c371f35d, baseline lines 369-370 (`kotowskiOllivier_of_leaves`, open-predicate and buried-conditional,
   census merge 63f147d7b).  No lane row names `kotowskiOllivier_of_leaves` any more; ko-closed dropped it at
   2d25ebab5.  Row LINE:1675 now names `kotowskiOllivier_closed` and `Hyperbolic.sharpExistence_closed`, and drops
   `kotowskiOllivier_of_pinched`, which has a binder.  Census is asked to retire the two lines at its next merge.

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
- nm-endpoints (~06:00): the rows that waited on `hpinch` now wait on wall 1 only.  (~07:10): split proposal for item 2.
- kh-cckw: the every-X HC6 is `Systolic.mirrorFold`.  This corrects my earlier name `mirrorFoldStatement`.
- sec2-sentences: docstring fixed (4be3a3a5c).

## NEXT
Await nm-endpoints' reply on item 2, then send census the old → new names.  Census retires baseline lines 369-370.
No Prop is owned.
