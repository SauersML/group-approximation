# simple-group (lane report, 2026-09-12)

Scope: the finitely presented, torsion-free, infinite simple group of the Fournier-Facio paragraph
(tex 1675–1685), with no literature inputs: Hyde–Lodha's `Q₂ = [Γ₂, Γ₂]`. The simplicity half is
fff-quotient's (`isSimpleGroup_qTwo_closed`, `qTwo_torsionFree`, `infinite_qTwo`). This lane owns the
Higman–Thompson layer, the finite-presentation tools, Lemma 4.4 and Theorem 4.8.

## Compiled and landed (all green in probes)
- Presentations: `DoubleCosetFinitePresentation.isFinitelyPresented_of_doubleCosets` (2-dimensional
  Brown criterion over `G/H`), `FinitePresentationExtension.isFinitelyPresented_of_normal` (P. Hall),
  `FGAbelianFinitePresentation`, `CasingPair.isFinitelyPresented_of_casingPair` (HL Lemma 4.2),
  `AscendingHNNRecognition` (HL Lemma 2.3 = GMSW 3.1, with finite presentation).
- Higman–Thompson `F_n` (`HigmanThompson/`): `GridAffine`, `Generators`, `BrownPresentation`
  (`brownF_isFinitelyPresented`), `UniformWords`, `GeometricF` (`geoF_eq_brownF`), `CompactE`,
  `CompactConj`, `CompactTrunc`, `CompactRangeA/B` (`geoFEquivCompactF`, `compactF_isFinitelyPresented`),
  `PLMoves`, `ResidueInvariance`, `CompactCore` (`isSimpleGroup_commutator_compactCore`),
  `CompactCoreGerms` (`commutator_compactF_eq`), `RstabIso` (HL Lemma 3.3, second half), `Proximal`
  (HL Lemma 3.3, first half), `Orbits` (HL Proposition 3.5, Lemma 3.6), `RstabGerms` (HL Lemma 4.4).
- `HydeLodha/`: `StrictMonoTorsionFree`, `HigmanEpstein`, `CommutatorGeneration`, `QTwoBrownStab`
  (vertex and edge stabilizers, `isFinitelyPresented_of_hom_int`), `QTwoBrownCover` (finitely many
  double cosets), `QTwoBrown` (`isFinitelyPresented_of_stabK_triangle`).

## On main, probe running
- `HydeLodha/QTwoFinitelyPresented`: Theorem 4.8 and `FinitelyPresentedInfiniteSimpleStatement` over the
  named hypotheses `StabKFinitelyPresented` (HL Proposition 4.7, fff-quotient) and `VertexHTriangle`
  (triangle count, go-lemma42, `QTwoBrownTriangle`).

## Residual
`isFinitelyPresented_stabK` and `vertexH_triangle`. When both land, `isFinitelyPresented_qTwo` and the
closed `finitelyPresentedInfiniteSimpleStatement` are one-line terms in `QTwoFinitelyPresented`.

## Census
No row yet: the printed sentence is graded through `FournierFacioParagraph`, which also needs the
hull-* and kh-* leaves; these modules are the proof of the cited group, not sentence carriers.
