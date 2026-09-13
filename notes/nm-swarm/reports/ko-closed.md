# ko-closed — the Kotowski–Ollivier input `hKO` from `GHB(7)` (lane ko-closed, clone thm-e, 2026-09-13)

Predecessor: kh-hyperbolic (dead; report `kh-hyperbolic.md`).  Target: `Kazhdan/KotowskiOllivierClosed.lean`,
closed `kotowskiOllivier_closed : TheoremC.KotowskiOllivierStatement`.

## STATE (09-13 ~04:55)
ONE residual leaf: `GroupApproximation.Systolic.MirrorFoldPinchedStatement GroupApproximation.KMSGroup.CCKW.cosetComplex`
(`GGT/SystolicDiscMirrorFoldCases.lean:102`), lane fff-periodic (`GGT/SystolicDiscMirrorFoldPinched.lean`, not on main yet).
- hzip closed on main: `CCKW.zipSpur_cosetComplex` (`GGT/SystolicDiscZip.lean`, 8389a0e6c, kh-torsion).
- hT6 drops out: `sharpExistence_ghb7_of_zipFoldHyp hzip hfold hhyp` (`Kazhdan/CCKWSystolicInvariantClique.lean`) needs only
  hzip, hfold at the coset complex; `hhyp := GHBQuotient.isHyperbolicGroup_ghb7_of_zipFold hzip hfold`.
- hfold = `mirrorFoldStatement_of_cases (mirrorFoldDistinct X) hpinch`; Distinct is CLOSED (below).

## LANDED (all GREEN, all wire-queued)
| module | SHA | probe |
|---|---|---|
| `Kazhdan/KotowskiOllivierClosed` (`kotowskiOllivier_of_leaves`) | c5a8ae8fb | 0913-011617-71747 |
| `GGT/SystolicDiscMirrorFoldCases` (Distinct/Pinched Props, `mirrorFoldStatement_of_cases`, `faceOf_alpha_ne_of_inner`) | 0fb6f2305 | green |
| `GGT/SystolicDiscMirrorFoldSteps` (`digonBack`, `CycleDisc.exists_of_embed`) | 79b8c51c8 | green |
| `GGT/SystolicDiscMirrorFoldQuad` (`MirrorQuad`, three moves, `planar3`, `faceCount_add_two`) | b110363ae | 0913-041349-71786 |
| `GGT/SystolicDiscMirrorFoldEmbed` (`tau`, `tau_facePerm`, `tau_injective`, `tau_cases`, `exists_tau_eq_of_ne`) | 781dcb8bf | 0913-042826-7309 |
| `GGT/SystolicDiscMirrorFoldDistinct` (`mirrorFoldDistinct`) | 81b06b43e | 0913-044647-45237 |

`theorem mirrorFoldDistinct (X : TriangleComplex V) : MirrorFoldDistinctStatement X`; `#print axioms`: propext,
Classical.choice, Quot.sound.

## ONE-LEAF REDUCTION (GREEN 0913-045023-55941, base e6dc0d444)
`kotowskiOllivier_of_pinched (hpinch : Systolic.MirrorFoldPinchedStatement CCKW.cosetComplex) :
Manuscript.NonMF.TheoremC.KotowskiOllivierStatement` in `Kazhdan/KotowskiOllivierClosed.lean` (rooted module; new
imports `CCKWSystolicInvariantClique`, `SystolicDiscZip`, `SystolicDiscMirrorFoldDistinct`, all on main).  Proof:
`sharpExistence_ghb7_of_zipFoldHyp CCKW.zipSpur_cosetComplex hfold (GHBQuotient.isHyperbolicGroup_ghb7_of_zipFold
CCKW.zipSpur_cosetComplex hfold)`, `hfold := mirrorFoldStatement_of_cases (mirrorFoldDistinct _) hpinch`.
`#audit_axioms`: propext, Classical.choice, Quot.sound.  Landed normally after the green probe.  Importer on main:
`Manuscript/NonMF/TheoremCAssemblyKOLeaves.lean` (already imports `CCKWSystolicInvariantClique`).

## hfold SPLIT (Option A, agreed with fff-periodic)
Setup: `d : a→b` in the inner face `[d, d1, d2]`, `alpha d` in `[alpha d, e1, e2]`, third corners with one label.
- DISTINCT (ko-closed, CLOSED): delete the edge of `d` (square), fold `d2` onto `alpha e1` (`FoldMap.IsFoldable`, the
  two ends differ), delete the digon edge `e2''`.  The final map embeds in the disc by `tau` along face rotation, reads
  labels compatibly and covers the exterior cycle, so it is a cycle disc with the same boundary and two faces fewer.
- PINCHED (fff-periodic): edge deletion, `VertexJoin`, restriction to the outer component, digon deletion.
- Final module `GGT/SystolicDiscMirrorFold.lean` (ko-closed): `mirrorFoldStatement X :=
  mirrorFoldStatement_of_cases (mirrorFoldDistinct X) (mirrorFoldPinched X)`, once Pinched lands.

## ORPHANS
`Kazhdan/KotowskiOllivierLeaves.lean` → ko-closed.  VERDICT (accepted by the lead): leave it; no deletion.  Nothing on main
imports it.

## NEXT
1. Green probe of `kotowskiOllivier_of_pinched`, normal landing, census row LINE:1675 updated to the single leaf.
2. On fff-periodic's `mirrorFoldPinched (X) : MirrorFoldPinchedStatement X`: `GGT/SystolicDiscMirrorFold.lean` and
   the binder-free endpoint `kotowskiOllivier_closed : TheoremC.KotowskiOllivierStatement := kotowskiOllivier_of_pinched
   (mirrorFoldPinched _)`, `#audit_closed_axioms`, then hand to theoremc-retire and nm-endpoints.
