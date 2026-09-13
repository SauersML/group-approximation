# simple-group (lane report, 2026-09-13)

Scope: the finitely presented, torsion-free, infinite simple group of the Fournier-Facio paragraph
(tex 1675–1685), with no literature inputs: Hyde–Lodha's `Q₂ = [Γ₂, Γ₂]`. The simplicity half is
fff-quotient's (`isSimpleGroup_qTwo_closed`, `qTwo_torsionFree`, `infinite_qTwo`). This lane owns the
Higman–Thompson layer, the finite-presentation tools, Lemma 4.4, Theorem 4.8 and the Lemma 4.6 /
Proposition 4.7 assembly (roster: integrator of hW).

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
  `finitelyPresentedInfiniteSimpleStatement_of_stabK` over Proposition 4.7 alone.
- `HydeLodha/QTwoLemmaFourSixCaseOne` (44d75dddd, probe 0912-100944-94062): `upsilonc`,
  `commutator_upsilon_le_upsilonc`, `upsilon_commutator_inter_upsilonc`, `pow_conj_mem_commutator_upsilon`.
- `HydeLodha/QTwoLemmaFourSixGenerators` (56aca9630, probe 0913-015349-13908): repaired at the pin;
  `exists_twisted_generators` (`⟨s_i u_i⁻¹ s_i⁻¹ u_i⟩ ≅ F_6` with commutator subgroup `Υ_{Γ₂}(J₀)'`).
- `HydeLodha/QTwoLemmaFourSixStatements` (232d6b12b, compiled): the piece Props
  `LemmaFourSixDynamicsStatement` (hl-lemma46) and `LemmaFourSixCaseOneStatement`.

## Landed with this report (probe 0913-021204-99418, propext, Classical.choice, Quot.sound)
- `HydeLodha/QTwoLemmaFourSixAssembly` (new): `lemmaFourSixCaseOne_of_dynamics` (`N = ⟨f, H⟩` is an
  ascending HNN extension of `H ≅ F_6`, and the Claim puts `Υ_{Γ₂}(I)'` in `N`),
  `isFinitelyPresented_upsilon_long_unit_of_caseOne`, `isFinitelyPresented_upsilon_long_of_caseOne`
  (`|I| = 1` by an ascending HNN extension over `Υ_Γ([a + λ, a + 1])`), `upsilonFinitelyPresented_of_caseOne`
  and `upsilonFinitelyPresented_of_dynamics` (Lemma 4.6). `|I| < 1` is consumed from kh-ejz's
  `QTwoLemmaFourSixTransfer` (58cfe133e). The `|I| = 1` lemmas fill the roster's fff-quotient slot, so no
  separate `|I| = 1` Prop is needed.
- `HydeLodha/FinitelyPresentedInfiniteSimpleClosed` (232d6b12b + edit):
  `stabKFinitelyPresented_of_upsilon`, `finitelyPresentedInfiniteSimpleStatement_of_upsilon`,
  `finitelyPresentedInfiniteSimpleStatement_of_dynamics`.

## Residual
Only hl-lemma46's `LemmaFourSixDynamicsStatement`: for grid `0 < a < b < 1`, an `f ∈ Υ_{Q₂}([a, b])` with
slope `6` at `a⁺`, grid `c < d` and `a < e₁ < c < d < e₂ < b` with `c ≤ f e₁`, `f e₂ ≤ d`, every
`k ∈ Υ^c_{Γ₂}([a, b])` conjugated by some `f^n` into `Υ^c_{Γ₂}([c, d])`, and six `s_i ∈ Υ_{Q₂}([e₁, e₂])`
moving `perIoo c d` off itself and off each other. When it lands, `theorem finitelyPresentedInfiniteSimple_closed :
FinitelyPresentedInfiniteSimpleStatement := finitelyPresentedInfiniteSimpleStatement_of_dynamics ...` goes
in `FinitelyPresentedInfiniteSimpleClosed` with `#audit_closed_axioms`, and the module is queued for wiring.

## Census
No row yet: the printed sentence is graded through `FournierFacioParagraph`, which also needs the
hull-* and kh-* leaves; these modules are the proof of the cited group, not sentence carriers.
