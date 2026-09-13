# ko-closed — the Kotowski–Ollivier input `hKO` from `GHB(7)` (lane ko-closed, clone thm-e, 2026-09-13)

Predecessor: kh-hyperbolic (dead; report `kh-hyperbolic.md`).  Target: `Kazhdan/KotowskiOllivierClosed.lean`,
first `kotowskiOllivier_of_leaves`, then the closed `kotowskiOllivier_closed : TheoremC.KotowskiOllivierStatement`.

## LANDED
- c5a8ae8fb: new `GroupApproximation/Kazhdan/KotowskiOllivierClosed.lean` (landed unverified first).
- Probe 0913-011617-71747 (base e499fdc3e): `PROBE GREEN`, `BUILT GroupApproximation.Kazhdan.KotowskiOllivierClosed`.
  The normal landing reports `NOTHING TO LAND`: the bytes on main are the probed bytes.
- Wire queue: `GroupApproximation.Kazhdan.KotowskiOllivierClosed ko-closed c5a8ae8fb`.

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

## RESIDUAL: the three leaves (exact Props)
1. `hzip : GroupApproximation.Systolic.ZipSpurStatement GroupApproximation.KMSGroup.CCKW.cosetComplex`
   (`GGT/SystolicDisc.lean:421`): `∀ p q u v, TriangulatedDisc X (p ++ u :: v :: u :: q) →
   Nonempty (TriangulatedDisc X (p ++ u :: q)) ∨ p ++ u :: q = [u]`.  Owner kh-torsion.  On main:
   `GGT/SystolicDiscZipFold.lean` (3e86a1d89), a draft of the fold case (`CycleDisc.zip_fold`).  No producer yet.
2. `hfold : GroupApproximation.Systolic.MirrorFoldStatement GroupApproximation.KMSGroup.CCKW.cosetComplex`
   (`GGT/SystolicDisc.lean:432`).  Owner fff-periodic.  No module on main or in the shared tree
   (`GGT/SystolicDiscMirrorFold.lean` does not exist).
3. `hT6 : GroupApproximation.KMSGroup.CCKW.SystolicInvariantCliqueStatement` (`Kazhdan/GHBSharpExistence.lean:34`),
   stated for every triangle complex.  Owner kh-cckw.  On main: `Dismantlable.exists_invariantClique`
   (`GGT/SystolicDismantlable.lean`) and `dismantlable_of_forall_dist_le` over `ProjectionClique`, `TriangleCondition`,
   `NoInducedFourCycle`, `NoInducedFiveCycle` (`GGT/SystolicBallDismantlable.lean`).  The graph conditions come from
   `noInducedFourCycle_of_linksSixLarge hfill hfold h6`, `noInducedFiveCycle_of_linksSixLarge`
   (`GGT/SystolicProjection.lean`) and `projectionClique_of_linksSixLarge hfill hfold h6 hconn`
   (`GGT/SystolicProjectionClique.lean`, in the shared tree only, not listed by any lane).  The assembly
   `exists_invariantClique_of_neighborSet_finite` exists nowhere yet.

The route to hT6 needs `FillingStatement X` and `MirrorFoldStatement X` at an ARBITRARY triangle complex `X`, and
`fillingStatement_of_simplyConnected hsc ha hb hc hd` (`GGT/SystolicDiscFilling.lean:126`) takes
`hd : ZipSpurStatement X`.  So the zip and fold producers should be stated for every `X` (with whatever hypotheses
the systolic class supplies), not only at `CCKW.cosetComplex`.  Both leaves feed hyperbolicity and the fixed-clique
theorem.

## ORPHANS in the shared tree (not on main, not in any lane's .files; 09-12 ~10:52)
- `Kazhdan/KotowskiOllivierLeaves.lean`: the same reduction (`kotowskiOllivierStatement_of_leaves`) and
  `TorsionFreeKOLeaves.*_of_hullKOLeaves` endpoint forms over hgreendlinger, hbridge, hzip, hfold, hT6, hW.
- `Manuscript/NonMF/TorsionFreeKOLeaves.lean`: endpoint forms over hT6 and hhyp.
- `GGT/SystolicProjectionClique.lean`: `projectionClique_of_linksSixLarge`, needed for hT6.

## NEXT
- `kotowskiOllivier_closed : TheoremC.KotowskiOllivierStatement` in the same module, one application, once the three
  leaves land.
- Consumers: theoremc-retire (`TheoremCAssembly` :653) and nm-endpoints use `kotowskiOllivier_of_leaves`.
