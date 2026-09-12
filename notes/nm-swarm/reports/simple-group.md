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

- `HydeLodha/QTwoFinitelyPresented` (47c4e98a0, probe 0912-092138-12304): Theorem 4.8 and
  `FinitelyPresentedInfiniteSimpleStatement` over the named hypotheses `StabKFinitelyPresented` (HL
  Proposition 4.7, fff-quotient) and `VertexHTriangle`.  The triangle count is discharged by
  `vertexHTriangle hQ hΓ` (go-lemma42's `vertexH_triangle`, `QTwoBrownTriangle`), giving
  `isFinitelyPresented_of_qTwo_le_of_stabK`, `isFinitelyPresented_qTwo_of_stabK` and
  `finitelyPresentedInfiniteSimpleStatement_of_stabK` over Proposition 4.7 alone.

## Residual
Only `StabKFinitelyPresented Γ := ∀ K : Set ℚ, K.Finite → K.Nonempty → (∀ k ∈ K, Dyadic6 k) →
Group.IsFinitelyPresented ↥(stabK Γ K)` (fff-quotient's `isFinitelyPresented_stabK`).  When it lands,
`isFinitelyPresented_qTwo` and the closed `finitelyPresentedInfiniteSimpleStatement` are one-line terms
in `QTwoFinitelyPresented`.

## In progress
Two Lemma 4.6 pieces for fff-quotient's Proposition 4.7, with the exact statements fff-quotient sent:
- (a) `HydeLodha/QTwoLemmaFourSixCaseOne` (44d75dddd, green in probe 0912-100944-94062): `upsilonc`
  (`Υ^c`), `commutator_upsilon_le_upsilonc`, `upsilon_commutator_inter_upsilonc`
  (`Υ_{Γ₂}(I)' ∩ Υ^c_{Γ₂}(J₀) = Υ_{Γ₂}(J₀)'`, Lemma 4.4 through `perHom`) and
  `pow_conj_mem_commutator_upsilon` (tex 904–905).
- (c) `HydeLodha/QTwoLemmaFourSixGenerators` (landed unverified 7db72cfc1, probe running):
  `brownRels_le_commutator`, `exists_mulEquiv_closure_mul`
  and `exists_twisted_generators` (`⟨s_i u_i⁻¹ s_i⁻¹ u_i⟩ ≅ F_6` with commutator subgroup `Υ_{Γ₂}(J₀)'`,
  tex 889–892).

## Census
No row yet: the printed sentence is graded through `FournierFacioParagraph`, which also needs the
hull-* and kh-* leaves; these modules are the proof of the cited group, not sentence carriers.
