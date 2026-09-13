# ko-closed — the Kotowski–Ollivier input `hKO` from `GHB(7)` (lane ko-closed, clone thm-e, 2026-09-13)

Predecessor: kh-hyperbolic (dead; report `kh-hyperbolic.md`).  Target: `Kazhdan/KotowskiOllivierClosed.lean`,
closed `kotowskiOllivier_closed : TheoremC.KotowskiOllivierStatement`.

## STATE (09-13 ~05:30)
ONE residual leaf: `GroupApproximation.Systolic.MirrorFoldPinchedStatement GroupApproximation.KMSGroup.CCKW.cosetComplex`
(`GGT/SystolicDiscMirrorFoldCases.lean:102`), lane fff-periodic (`GGT/SystolicDiscMirrorFoldPinched.lean`, not on main yet).
- Pinched progress on main: `GGT/SystolicDiscMirrorFoldPinchedStage.lean` (08ae1c587, fff-periodic).  Its
  `FoldStage.exists_disc_of_pinch` turns a pinch configuration in a stage with boundary `γ` into a disc with boundary
  `γ` and at least three faces fewer.  The producer `mirrorFoldPinched (X) : MirrorFoldPinchedStatement X` is still missing.
- hzip closed on main: `CCKW.zipSpur_cosetComplex` (`GGT/SystolicDiscZip.lean`, 8389a0e6c, kh-torsion).
- hT6 is not needed.  `sharpExistence_ghb7_of_zipFoldHyp hzip hfold hhyp` (`Kazhdan/CCKWSystolicInvariantClique.lean`)
  takes only hzip and hfold at the coset complex, with `hhyp := GHBQuotient.isHyperbolicGroup_ghb7_of_zipFold hzip hfold`.
- hfold = `mirrorFoldStatement_of_cases (mirrorFoldDistinct X) hpinch`.  Distinct is CLOSED (below).

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

Census row LINE:1675 (`kotowskiOllivier_of_pinched`, partial, one leaf): f2f00aada.

`theorem mirrorFoldDistinct (X : TriangleComplex V) : MirrorFoldDistinctStatement X`; `#print axioms`: propext,
Classical.choice, Quot.sound.  dgo-geometric independently audited the Prop as true.

## ONE-LEAF REDUCTION (GREEN 0913-045023-55941, base e6dc0d444)
`kotowskiOllivier_of_pinched (hpinch : Systolic.MirrorFoldPinchedStatement CCKW.cosetComplex) :
Manuscript.NonMF.TheoremC.KotowskiOllivierStatement` in `Kazhdan/KotowskiOllivierClosed.lean` (rooted module).  Proof:
`sharpExistence_ghb7_of_zipFoldHyp CCKW.zipSpur_cosetComplex hfold (GHBQuotient.isHyperbolicGroup_ghb7_of_zipFold
CCKW.zipSpur_cosetComplex hfold)`, `hfold := mirrorFoldStatement_of_cases (mirrorFoldDistinct _) hpinch`.
`#audit_axioms`: propext, Classical.choice, Quot.sound.  Consumers on main: `Manuscript/NonMF/TheoremCAssemblyKOLeaves.lean`
(`_of_leastAreaKOLeaves`, through `kotowskiOllivier_of_leaves`).  `hKO` is a binder of
`TheoremC.manuscriptTorsionFreeFullMFRadical_of_leastAreaInputs` and `..._Simplified_of_leastAreaInputs` (TheoremCAssembly).

## hfold SPLIT (Option A, agreed with fff-periodic)
Setup: `d : a→b` in the inner face `[d, d1, d2]`, `alpha d` in `[alpha d, e1, e2]`, and the third corners carry one label.
- DISTINCT (ko-closed, CLOSED), in three moves:
  1. Delete the edge of `d`, which leaves a square.
  2. Fold `d2` onto `alpha e1` (`FoldMap.IsFoldable`: the two ends differ).
  3. Delete the digon edge `e2''`.

  The final map embeds in the disc by `tau` along face rotation, reads labels compatibly and covers the exterior
  cycle.  So it is a cycle disc with the same boundary and two faces fewer.
- PINCHED (fff-periodic): edge deletion, `VertexJoin`, restriction to the outer component, digon deletion.
  The stage move is on main (08ae1c587, above).
- Final module `GGT/SystolicDiscMirrorFold.lean` (ko-closed, draft ready): `mirrorFoldStatement X :=
  mirrorFoldStatement_of_cases (mirrorFoldDistinct X) (mirrorFoldPinched X)`, to land once Pinched does.

## ORPHANS
`Kazhdan/KotowskiOllivierLeaves.lean` → ko-closed.  VERDICT (accepted by the lead): leave it; no deletion.  Nothing on main
imports it.

## COORDINATION
- kh-cckw (~05:25): Distinct is closed and the hT6-free KO is on main, so their split offer needs no action.  The every-X
  `Systolic.mirrorFoldStatement` from the final module will serve `CCKW.systolicInvariantClique_of_zipFold`.

## NEXT
1. When fff-periodic's `mirrorFoldPinched (X) : MirrorFoldPinchedStatement X` lands, add these to
   `Kazhdan/KotowskiOllivierClosed.lean`:
   - the module `GGT/SystolicDiscMirrorFold.lean`;
   - the binder-free endpoint `kotowskiOllivier_closed : TheoremC.KotowskiOllivierStatement :=
     kotowskiOllivier_of_pinched (mirrorFoldPinched _)`, checked with `#audit_closed_axioms`.

   Then set census row LINE:1675 to closed and hand the endpoint to theoremc-retire and nm-endpoints.
