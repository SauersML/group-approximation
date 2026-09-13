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

## Dropped: Hull Corollary 7.3 draft
cite-hull landed Corollary 7.3 (`Manuscript/NonMF/HullCorollary73`, a2299c82c, wired 830b05464) and
Corollary 7.4 (c6e0b6c33). The simple-group draft of 7.3 was never landed, so nothing needs retiring.

## W1: corner-to-corner insertion on section families (09-13)
The lead assigned the corner-to-corner insertion transported to `RealizedSectionFamily`. It is one of the
respell surgeries under hull-unbound's `GloballyDistinguishedSectionFamily.ChainRespellInput`
(`OsinLemma94ChainRespell`; target Prop `CornerInsertionInput`). The lead then asked for the two missing
pieces in modules owned by this lane.
- `VanKampen/Estimating/DiscEmbeddingAwayUnbound` (first landed ff8e8fce9, probe 0913-094539-34824). A corner
  output carries a section family (`CornerOutput.retainedSection`) and a globally distinguished section family
  (`CornerOutput.retainedDistinguished`) to the inserted diagram, with the same weight and card, and
  `retainedDistinguished_unboundSum : (retainedDistinguished S R havoid).unboundSum = S.unboundSum`. The first
  landing duplicated five `DiscEmbeddingAway.regionCandidate_*` declarations of sec2-sentences' c652fa749
  (`OsinLemma94InsertionTransport`). The rewrite imports that module, keeps only the corner output section, and
  takes the unbound sum from `DiscEmbeddingAway.sum_unboundDarts_regionFamily_card`.
- `VanKampen/GFaceCornerDartCount` (997275cc0, probe 0913-095451-54209): `GEdgeWordSubdivision.Output.dartCount_add_two` (from
  `DiscExpansion.exists_old_dart`, `nodup`, `reverse`, `other_word`), `GFaceEdgeInsertion.dartCount_eq`
  (`+2`), `GFaceWordInsertion.exists_cell_output_dartCount` and `exists_corner_output_dartCount`
  (`∃ R : CornerOutput …, R.diagram.toCombMap.dartCount = Delta.toCombMap.dartCount + 2 * word.length`).

- `VanKampen/Estimating/OsinLemma94CornerInsertion` (f7538e223, probe 0913-123745-5546; the rewrite above landed in
  the same commit; queued for wiring): `GFaceWordInsertion.SplitOutput.dartCount_eq`
  (a split insertion adds exactly `2 * word.length` darts: the old darts, the path and the reversed path are
  disjoint), `SplitOutput.side_ne_outerFace`, `side_ne_cellFace`, and
  `GloballyDistinguishedSectionFamily.cornerInsertionInput : CornerInsertionInput`. The word goes in between the
  corners before and after `chain` (`GFaceWordInsertion.exists_split_corner_output`), and the family follows
  (`insertionTransport`). The transported chain runs along the prefix side and the walk across it runs along the
  suffix side. The inner joints keep valence two, because the walk across `chain` inside `rest ++ chain` never
  reaches the last dart of `rest`: no dart of `chain` lies across `chain`.

### Residual for `CornerInsertionInput`
None. `cornerInsertionInput : CornerInsertionInput` is closed (propext, Classical.choice, Quot.sound). The module
is not wired; it enters the root through hull-unbound's `ChainRespellInput` producer.
`SeparatingPathRemovalInput` belongs to another lane.
