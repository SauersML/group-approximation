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

- Shared core with `SeparatedCornerInsertionInput` (sec5-sentences' `OsinLemma94SeparatedInsertion`, b52230097): not
  landed, by the lead's ruling.
  - sec2-sentences had already landed `separatedCornerInsertionInput` in `OsinLemma94SeparatedInsertionProof` (619b70139).
    It is built on this module's helpers, and the two proofs repeat only about 40 lines of set-up.
  - The lead said to skip the core refactor and to leave this module's helpers untouched while that module is probed and
    wired.
  - The draft core `exists_corner_split_insertion` compiled green in probe 0913-130752-84082, with both Props derived from
    it. A second probe, 0913-131141-4967, was also green: it ran the core with only `cornerInsertionInput` derived, and
    also built `OsinLemma94SeparatedInsertionProof` and `OsinLemma94SectionResiduals` against it. The draft is kept at
    `$NM/backup/simple-group/OsinLemma94CornerInsertion.lean.0913-core-refactor`.

### Residual for `CornerInsertionInput`
None. `cornerInsertionInput : CornerInsertionInput` is closed (propext, Classical.choice, Quot.sound). The module is not
wired. Two modules import it: hull-unbound's `OsinLemma94SectionResiduals` (0087a5095) and sec2-sentences'
`OsinLemma94SeparatedInsertionProof` (619b70139). `SeparatingPathRemovalInput` belongs to another lane.

## W2: `GeodesicCollar.InsertStatement` (kh-torsion's `SurgeryGeodesicCollarAssembly`, a89b55a0d)
Assigned by the lead. kh-torsion was told before any Lean was written.
- The design splits the strip face along `g` with `GFaceWordInsertion.exists_split_corner_output`, between the corner at the
  head of `p` and the corner at the head of `q`:
  - The new face set is the suffix side together with the kept faces.
  - The transport comes from `CornerOutput.originalReplacement` and `ContiguityTransport`.
  - The collar is the inserted path.
- Path collision at 14:34: hull-bridge wrote `VanKampen/SurgeryGeodesicCollarInsert.lean` (registered in `hull-bridge.files`)
  over this lane's draft at the same path. That file is hull-bridge's, and this lane has not edited it since.
- The draft's Strip half (face membership, boundary iff, walk plan, statement plan) is kept at
  `$NM/backup/simple-group/SurgeryGeodesicCollarInsert.strip-and-statement.draft.lean`. It has never been compiled.
- Ruling (a), on this lane's recommendation: hull-bridge keeps `InsertStatement` and `SurgeryGeodesicCollarInsert.lean`. This
  lane sent hull-bridge the proof text as one message:
  - vertex `Nodup` via `internal_fresh` / `internal_vertex_eq_iff`;
  - the `IsBoundaryDart` iff for `path ++ r.map emb`;
  - `IsSimpleClosedWalk` for `r = []` and `r ≠ []`;
  - the `insertStatement` assembly (`hinv` via `hsymm` / `(D.fam i).inv_mem`).

### Residual for `InsertStatement`
None for this lane; the Prop is hull-bridge's. Nothing from W2 has landed.

## W3: Stage 1 of the collar, `GeodesicCollar.StripStatement` (binder 8 of the waist 8a07ad7d0)
Assigned by the lead: the Strip sub-module that hull-bridge had held, either the pinch step or the induction. kh-torsion owns
`StripStatement`.
- kh-torsion registered `VanKampen/SurgeryGeodesicCollarPinch.lean` in `kh-torsion.files` at 15:45, so this lane does not write
  there. kh-torsion has been asked whether it is building the pinch step. The design sent for the step: `PinchSplit.Input`
  on the doubled map, `x := alpha (embed (p.getLast _))`, `y := some none`, and the merged face cycle rotated by
  `q.length + 3`.
- This lane builds the induction in `VanKampen/SurgeryGeodesicCollarInduction.lean` (registered in `simple-group.files`):
  - `GeodesicCollar.StripStepStatement`, the pinch step: `Strip Delta S p (d :: r)` gives a transport to a strip along the
    image of `p ++ [d]`;
  - `stripAppend`: the step repeated along a list `t`, by induction on `t.length`, composing the transports with
    `Transport.trans`;
  - `stripStatement_of_step : StripStepStatement → StripStatement`: `stripSingleton` on the first dart, then `stripAppend`.
- Probe 0913-155533-35125 green (base cda0020eb, errors section empty, compiled md5 `210ab6ce…` = disk). Landed unwired: nothing
  consumes the module until a theorem for the step exists.

- Landed at cec4605ee. kh-torsion then replied that no Strip sub-module is open. It is writing the pinch step and the induction
  `stripStatement` in `SurgeryGeodesicCollarPinch.lean`, and hull-bridge takes the final `GeodesicCollarStatement` reduction.
  kh-torsion has the names of this module and can import it, proving only `stripStep : StripStepStatement`. Otherwise the module
  stays unused, and the lead decides whether to retire it. If both modules define `GeodesicCollar.StripStepStatement`, importing
  both breaks the build.

### Residual for `StripStatement`
None for this lane: the step and the Prop are kh-torsion's. `stripStatement_of_step stripStep : StripStatement` closes Stage 1
once some theorem `stripStep : StripStepStatement` exists. This lane has asked the lead for another item.
