# simple-group (lane report, 2026-09-13)

Scope: the finitely presented, torsion-free, infinite simple group of the Fournier-Facio paragraph
(tex 1675–1685), with no literature inputs: Hyde–Lodha's `Q₂ = [Γ₂, Γ₂]`. The simplicity half is
fff-quotient's (`isSimpleGroup_qTwo_closed`, `qTwo_torsionFree`, `infinite_qTwo`). This lane owns the
Higman–Thompson layer, the finite-presentation tools, Lemma 4.4, Theorem 4.8 and the Lemma 4.6 /
Proposition 4.7 assembly (roster: integrator of hW).

## hW closed (probe 0913-023517-12793, propext, Classical.choice, Quot.sound)
- `HydeLodha/FinitelyPresentedInfiniteSimpleClosed` (47b31bef8):
  `theorem finitelyPresentedInfiniteSimple_closed : FinitelyPresentedInfiniteSimpleStatement`, audited
  with `#audit_closed_axioms`. It applies `finitelyPresentedInfiniteSimpleStatement_of_dynamics` to
  hl-lemma46's `lemmaFourSixDynamics` (`QTwoLemmaFourSixDynamics`, de535e84c, probe 0913-021539-18816).
- Root-reachable: root-wire's wave c72bdfd5d imports `FinitelyPresentedInfiniteSimpleClosed` (bytes
  47b31bef8 included), and through it `QTwoLemmaFourSixAssembly` and `QTwoLemmaFourSixDynamics`.

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
- `HydeLodha/QTwoLemmaFourSixAssembly` (3e2e73c3d, probe 0913-021204-99418): `lemmaFourSixCaseOne_of_dynamics`
  (`N = ⟨f, H⟩` is an ascending HNN extension of `H ≅ F_6`, and the Claim puts `Υ_{Γ₂}(I)'` in `N`),
  `isFinitelyPresented_upsilon_long_unit_of_caseOne`, `isFinitelyPresented_upsilon_long_of_caseOne`
  (`|I| = 1` by an ascending HNN extension over `Υ_Γ([a + λ, a + 1])`), `upsilonFinitelyPresented_of_caseOne`
  and `upsilonFinitelyPresented_of_dynamics` (Lemma 4.6). `|I| < 1` is consumed from kh-ejz's
  `QTwoLemmaFourSixTransfer` (58cfe133e).
- `HydeLodha/FinitelyPresentedInfiniteSimpleClosed` (3e2e73c3d, same probe):
  `stabKFinitelyPresented_of_upsilon` (Proposition 4.7), `finitelyPresentedInfiniteSimpleStatement_of_upsilon`,
  `finitelyPresentedInfiniteSimpleStatement_of_dynamics`.

## Residual
None for hW. `FinitelyPresentedInfiniteSimpleStatement` is closed and reachable from the root on main
(c72bdfd5d); no wiring remains.

## Census
`metadata/nm-census-rows/simple-group.tsv` (copy of `$NM/rows/simple-group.tsv`): `LINE:1679 partial`,
naming the closed hW chain. It is graded `partial` because the printed sentence is the whole Fournier-Facio
construction (`G_0`, `Γ`, `t`, `J`); hW supplies only the finitely presented infinite simple group
isomorphic to `J`. The sentence as a whole is graded through `FournierFacioParagraph`, which also needs the
hull-* and kh-* leaves.

## Next
The lane's scope is finished; waiting for the lead to assign more work.
