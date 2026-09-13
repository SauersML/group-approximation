# ko-closed — the Kotowski–Ollivier input `hKO` from `GHB(7)` (lane ko-closed, clone thm-e, 2026-09-13)

Predecessor: kh-hyperbolic (dead; report `kh-hyperbolic.md`).  Target: `Kazhdan/KotowskiOllivierClosed.lean`,
first `kotowskiOllivier_of_leaves`, then the closed `kotowskiOllivier_closed : TheoremC.KotowskiOllivierStatement`.

## LANDED
- c5a8ae8fb: new `GroupApproximation/Kazhdan/KotowskiOllivierClosed.lean` (landed unverified first).
- Probe 0913-011617-71747 (base e499fdc3e): `PROBE GREEN`, `BUILT GroupApproximation.Kazhdan.KotowskiOllivierClosed`.
  The normal landing reports `NOTHING TO LAND`: the bytes on main are the probed bytes.
- Wire queue: `GroupApproximation.Kazhdan.KotowskiOllivierClosed ko-closed c5a8ae8fb`.
- 6d2856bc7: this report and census row `LINE:1675 partial`.

## THEOREM
```lean
namespace GroupApproximation.KMSGroup.KotowskiOllivierClosed
theorem kotowskiOllivier_of_leaves (hzip : Systolic.ZipSpurStatement CCKW.cosetComplex)
    (hfold : Systolic.MirrorFoldStatement CCKW.cosetComplex)
    (hT6 : CCKW.SystolicInvariantCliqueStatement) :
    Manuscript.NonMF.TheoremC.KotowskiOllivierStatement :=
  sharpExistence_ghb7_of_fixedCliqueHyp hT6
    (GHBQuotient.isHyperbolicGroup_ghb7_of_zipFold hzip hfold)
```
`#audit_axioms`: propext, Classical.choice, Quot.sound.  `TheoremC.KotowskiOllivierStatement` is
`Hyperbolic.SharpExistence` (an infinite, finitely presented, torsion-free hyperbolic group with property (T)).
Every other piece of the chain is proved and compiled on main: property (T) `hasKazhdanPropertyT_ghb7`, the orders
`card_U3_seven_le`, `card_U4_seven_le`, Tits' lemma `CCKWTits.cckwCosetComplex_simplyConnected` and `_connected`,
HC3(a–c) `Systolic.attachTriangleStatement`, `insertChordStatement`, `attachPendantStatement`, HC11
`CCKW.typedCountStatement_cosetComplex`, HC12 `GHBHyperbolicStokes.boundarySumStatement`.

Consumers on main: `Manuscript/NonMF/TheoremCAssemblyKOLeaves.lean` (4874b8162, unwired) composes `TheoremCAssembly`
with `kotowskiOllivier_of_leaves`; nm-endpoints' `TorsionFreeFourLeaves` (12e1d1af8) takes `hKO` and names it.

## RESIDUAL: the three leaves (exact Props)
1. `hzip : GroupApproximation.Systolic.ZipSpurStatement GroupApproximation.KMSGroup.CCKW.cosetComplex`
   (`GGT/SystolicDisc.lean:421`): `∀ p q u v, TriangulatedDisc X (p ++ u :: v :: u :: q) →
   Nonempty (TriangulatedDisc X (p ++ u :: q)) ∨ p ++ u :: q = [u]`.  Owner kh-torsion (systolic-counts takes a
   case).  On main: `GGT/SystolicDiscZipFold.lean` (3e86a1d89), the fold case `CycleDisc.zip_fold`.  No producer yet.
2. `hfold : GroupApproximation.Systolic.MirrorFoldStatement GroupApproximation.KMSGroup.CCKW.cosetComplex`
   (`GGT/SystolicDisc.lean:432`).  Owner fff-periodic; ko-closed takes a case (split proposed 09-13, below).
   No module on main or in the shared tree.
3. `hT6 : GroupApproximation.KMSGroup.CCKW.SystolicInvariantCliqueStatement` (`Kazhdan/GHBSharpExistence.lean:34`),
   stated for every triangle complex.  Owner kh-cckw.  On main: `Dismantlable.exists_invariantClique`
   (`GGT/SystolicDismantlable.lean`) and `dismantlable_of_forall_dist_le` over `ProjectionClique`, `TriangleCondition`,
   `NoInducedFourCycle`, `NoInducedFiveCycle` (`GGT/SystolicBallDismantlable.lean`).  The graph conditions come from
   `noInducedFourCycle_of_linksSixLarge hfill hfold h6`, `noInducedFiveCycle_of_linksSixLarge`
   (`GGT/SystolicProjection.lean`), `projectionClique_of_linksSixLarge hfill hfold h6 hconn`
   (`GGT/SystolicProjectionClique.lean`, 3cf9bd845) and `triangleCondition_of_linksSixLarge hfill hfold h6 hconn`
   (`GGT/SystolicTriangleCondition.lean`, shared tree only).  The assembly
   `exists_invariantClique_of_neighborSet_finite` exists nowhere yet.

The route to hT6 needs `FillingStatement X` and `MirrorFoldStatement X` at an ARBITRARY triangle complex `X`, and
`fillingStatement_of_simplyConnected hsc ha hb hc hd` (`GGT/SystolicDiscFilling.lean:126`) takes
`hd : ZipSpurStatement X`.  So the zip and fold producers should be stated for every `X`, not only at
`CCKW.cosetComplex`.  Both leaves feed hyperbolicity and the fixed-clique theorem.

## hfold SPLIT (proposed to fff-periodic 09-13; no Lean until agreed)
Setup: `d : a→b` lies in the inner face `[d, d1 : b→c, d2 : c→a]`, and `alpha d` in the inner face
`[alpha d, e1 : a→c', e2 : c'→b]`, with the labels of `c` and `c'` equal.  The two faces are distinct, because
triangle labels are distinct.
- DISTINCT, `D.third d ≠ D.third (D.map.alpha d)`:
  1. `EdgeDeletion` of `d` merges the two faces into the quad `[d1, d2, e1, e2]` (`planar_of_neFace`).
  2. `FoldMap.IsFoldable (p := d1) (d := d2) (e := e1)` holds since `c ≠ c'`, leaving the digon `[d1, e2]`.
  3. `EdgeDeletion` of `e2` removes the digon.
  The boundary is unchanged: `alpha e1` is relabelled `d2` and `alpha e2` is relabelled `d1`, with equal labels.
  The face count drops by 2 (`faceCount_balance_of_neFace`, `FoldMap.faceCount_eq`).
- PINCHED, `D.third d = D.third (D.map.alpha d)`:
  1. `EdgeDeletion` of `d`.
  2. `VertexJoin` splits `c` at its two corners on the merged face, giving Euler characteristic 4.
  3. Restrict to the component of the outer face (`CombMapInvariantRestrict.restrict`, `restrict_planar_of_euler_four`).
  4. Delete its digon.
- Modules:
  - `GGT/SystolicDiscMirrorFoldCases.lean`: `MirrorFoldDistinctStatement X`, `MirrorFoldPinchedStatement X`, and
    `mirrorFoldStatement_of_cases`.
  - `GGT/SystolicDiscMirrorFoldDistinct.lean` and `GGT/SystolicDiscMirrorFoldPinched.lean`.
  - `GGT/SystolicDiscMirrorFold.lean`: `theorem mirrorFoldStatement (X) : MirrorFoldStatement X`.
- Offer A (fff-periodic has not started): ko-closed owns Cases, Distinct and the final module; fff-periodic takes
  Pinched.  Offer B (fff-periodic has started): fff-periodic keeps the Prop and ko-closed takes the other case.

## ORPHANS (landed by the lead 3cf9bd845, unverified; owners told 09-13)
- `GGT/SystolicProjectionClique.lean` → kh-cckw.
- `Manuscript/NonMF/TorsionFreeKOLeaves.lean` → nm-endpoints (`*_of_leastAreaFixedCliqueHyp`,
  `*_of_hullFixedCliqueHyp`, over hT6 and hhyp; no name clash).
- `Kazhdan/KotowskiOllivierLeaves.lean` → ko-closed.  VERDICT: move nothing, retirable; no deletion landed.
  - `kotowskiOllivierStatement_of_leaves` is the same proof term as `kotowskiOllivier_of_leaves`.
  - Its seven `TorsionFreeKOLeaves.*_of_leastAreaKOLeaves/_of_hullKOLeaves` forms equal TorsionFreeFourLeaves
    `*_of_fourLeaves` over `hKO`, composed with `kotowskiOllivier_of_leaves`.
  - Nothing on main imports it.

## NEXT
- On fff-periodic's reply: land the Cases module (Props and dispatch), then the agreed case module, probed through
  `nmprobe.sh`.
- `kotowskiOllivier_closed : TheoremC.KotowskiOllivierStatement` in the same module, one application, once the three
  leaves land.
