# One-sided Kazhdan transport: statement-to-declaration ledger

One row per numbered statement and per displayed equation of
`non_mf_groups_exist.tex` (*One-sided Kazhdan transport and MF radicals*).
Each row names the Lean declaration that carries it.
`scripts/check_onesided_transport_ledger.py` enforces four things
mechanically:

1. every declaration named below exists in the Lean development;
2. every declaration named below is printed in
   `GroupApproximation/Endpoint/OneSidedTransportAudit.lean`, so its axiom
   closure and its zero-input status are checked by the build;
3. every `#audit_closed_axioms` line of that audit file appears below, so the
   ledger cannot silently omit a headline;
4. every `\label{...}` of the manuscript other than the section labels has a
   row, so a new numbered statement cannot be printed without one.

There is no "proof is analogous" row and no prose claim stronger than the
declaration receiving the badge.

## What the three statuses mean

`closed` — the declaration is printed with `#audit_closed_axioms`.  That macro
fails the build both when the axiom closure reaches beyond `propext`,
`Classical.choice`, `Quot.sound` and when the declaration's type begins with a
caller-supplied binder.  A green build is therefore a machine proof that the
row is unconditional: the manuscript's quantifiers live inside a named `Prop`,
and nothing is accepted as mathematical input from a caller.

`conditional` — the declaration is printed with the weaker `#audit_axioms` and
is **not** printed with the closed macro.  Its type begins with a binder.  Five
different things put a binder there, and this ledger separates them by name
rather than by status, because the status vocabulary cannot:

* **manuscript data the statement is universally quantified over** — the
  ambient group, the coefficient ring, the Leavitt family, the homomorphism.
  Rows `eq:intrinsic-defect`, `eq:matrix-compression`,
  `eq:defect-functoriality`, `eq:corner-conjugation` and `eq:amalgam` are of
  this kind, and each is strictly more general than what the manuscript
  prints.  Nothing is assumed in them; `#audit_closed_axioms` rejects them
  only because a definition or a lemma over arbitrary data cannot have an
  empty telescope.  Every one of the five is *used* by a closed row: the
  defect rows by `manuscriptCompleteOneSidedCompressionCriterion` and
  `manuscriptDefectSaturation`, the Leavitt rows by
  `RankTwelveEndpoint.printedDefectConfiguration`, and `eq:amalgam` by
  `manuscriptPrescribedMFQuotients`.  So none of the five can be wrong without
  a closed row failing.
* **a universe-polymorphic support theorem.**  Lean propositions cannot bind a
  universe level, so `rankTwelve_propertyT_universe_profile` is audited as a
  theorem at arbitrary `v`.  It has no mathematical hypothesis: it strengthens
  the already closed property-`(T)` clauses and does not add a numbered claim.
* **generic coefficient-ring support.**  `BinaryLeavitt.center_eq_bot` is
  stated over an arbitrary field, and `BinaryLeavitt.central_units_trivial`
  quantifies over the central unit it classifies.  Both are unconditional
  support for the manuscript's ring-centre step; neither asserts group
  simplicity or discharges root detection.
* **generic partial root-extraction support.**  The coefficient-separation,
  double-commutator, and transvection-extraction theorems quantify over the
  ring, index type, normal subgroup, and their explicit matrix configurations.
  Together with the separately proved dense and diagonal branches they feed
  the closed generic root-detection theorem; these individual configuration
  lemmas remain conditional only because their arbitrary input data occur as
  leading binders.
* **generic congruence-subgroup support.**  The relative-elementary and
  congruence endpoints, the `GL` centre computation, and the final simplicity
  assembly quantify over the ring and index type.  The assembly retains
  Preusser's normal-subgroup sandwich as an explicit leading hypothesis; it is
  a precise reduction, not a proof of the manuscript's simplicity claim.

`MISSING` — no declaration in the development proves the row.  No current row
has this status.  A `MISSING`
row's target may exist as a *statement* (a `def ... : Prop`); the gate refuses
to let it be printed in the audit under either macro, and refuses to let it
become a `theorem` without the row being updated.

Manuscript state pinned at authoring time: 1234 lines,
`sha256 0cc88f62...d8d7a778a`, 29 labelled statements.  The table has 94 rows
-- 70 `closed`, 24 `conditional`, 0 `MISSING`, naming 90 distinct declarations.
One row appears for each label, and sixty-five further rows either split a
printed theorem into separately audited constituents or cover an unnumbered
printed sentence. Four declarations each appear twice: the introduction repeats
a Section 3 corollary, the simplicity input is recorded both where Theorem B
consumes it and where Proposition `prop:simple` is printed, and the same generic
double-commutator computation and membership lemma instantiate both the sparse
and dense displayed equations.

All **15 of the manuscript's 15 numbered statements are closed**.
`RankTwelveEndpoint.manuscriptPropositionSimple` proves `prop:simple`, and
`manuscriptBinaryLeavittHeadline` proves full Theorem B including simplicity.
The separate closed row `manuscriptBinaryLeavittFullRadical` remains useful as
the hypothesis-free package of every headline clause except simplicity.
Re-pin after reviewing the rows an edit to the `.tex` touches.

## Rows

<!-- LEDGER-ROWS -->
| Paper | Lean declaration | Status |
| --- | --- | --- |
| `prop:mf-residual-calculus` MF residual calculus, on the literal MF closure | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptMFResidualCalculusLiteral` | closed |
| `prop:mf-residual-calculus` again, on the corona closure | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptMFResidualCalculus` | closed |
| Sec. 1 display, `cl_MF^G(N)` as the intersection of MF-target kernels, and as the quotient pullback | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptLiteralMFClosureIsQuotientPullback` | closed |
| Sec. 1 display, `Rad_MF(G) = cl_MF^G(1)` | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptMFRadicalIsLiteralClosureOfTrivial` | closed |
| Sec. 1, a full radical kills every homomorphism to an MF group | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptFullRadicalKillsMFTargets` | closed |
| Introduction, the norm matrix corona denominator is exactly the operator-norm `c₀` direct sum | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCoronaDenominator` | closed |
| Introduction, MF is equivalent to finite-dimensional asymptotically multiplicative and separating unitary models | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptMFUnitaryModels` | closed |
| Introduction, corona images are countable MF groups and MF targets embed in norm matrix coronas | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCoronaImagesAndTargets` | closed |
| `eq:intrinsic-defect` the compression-centralizer defect | `GroupApproximation.Manuscript.OneSidedMFRadical.printedDefect` | conditional |
| Theorem A `thm:compression-criterion`, all four printed clauses | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCompleteOneSidedCompressionCriterion` | closed |
| Theorem A, the three MF-radical clauses | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptOneSidedCompressionCriterion` | closed |
| Theorem A, fourth clause: every finite-dimensional linear representation over every field kills the defect | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedDefectFiniteDimensionalSterility` | closed |
| `eq:leavitt` the binary Leavitt relations, at the manuscript's ring | `GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.leavittFamily` | closed |
| Theorem B, closed simplicity input from `prop:simple` | `GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.manuscriptPropositionSimple` | closed |
| Theorem B `thm:headline`, every printed clause, simplicity included | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptBinaryLeavittHeadline` | closed |
| Theorem B minus the simplicity clause, hypothesis-free | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptBinaryLeavittFullRadical` | closed |
| Abstract headline, existence of a countable non-MF group | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCountableNonMFGroupExists` | closed |
| Abstract headline, refutation of “every countable group is MF” | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptNotEveryCountableGroupIsMF` | closed |
| Abstract headline at the equivalent `IsOperatorMF` predicate | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCountableNonOperatorMFGroupExists` | closed |
| Abstract realisation minus simplicity: a countable nontrivial Kazhdan group with full MF radical | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCountableKazhdanFullMFRadicalGroupExists` | closed |
| Abstract criterion: a saturated printed defect kills all MF-target maps and obstructs MF-ness | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSaturatedDefectKillsMFTargets` | closed |
| Theorem B, displayed conclusion `Rad_MF(H) = H` | `GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.rankTwelve_actualCoronaMFResidual_eq_top` | closed |
| Theorem B, structural clauses: nontrivial, countable, finitely generated, property (T), and `d` nontrivial and normally generating | `GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.closedStructuralProfile` | closed |
| Support for the existing Theorem B and `eq:compresses-L` property-`(T)` clauses: the rank-twelve group and its corner have real and complex property `(T)` at every representation universe | `GroupApproximation.rankTwelve_propertyT_universe_profile` | conditional |
| `eq:basic-defect` the Hilbert--Schmidt display of `cor:defect-hs` | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCompressionDefectHSInvisible` | closed |
| Sec. 1, faithful finite-dimensional, residually finite and finite-`L` sterility | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedDefectSterility` | closed |
| Sec. 1, the amenable clause: property (T) plus amenable gives finite, hence a trivial defect | `GroupApproximation.manuscriptAmenableKazhdanSterility` | closed |
| Theorem C `thm:prescribed-quotients` | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrescribedMFQuotients` | closed |
| `thm:commutant` finite-dimensional commutant rigidity | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptFiniteDimensionalCommutantRigidity` | closed |
| Remark after `thm:commutant`, finite dimensionality is essential | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCommutantFiniteDimensionalHypothesisIsEssential` | closed |
| Introduction's finite-subgroup chain: onto conjugation, transported centralizer, and trivial defect | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedAmenableCaseChain` | closed |
| Scope remark, a sofic and hyperlinear witness can have full MF and shadow residuals | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSoficityIsNotObstructedByFullRadicals` | closed |
| Scope remark, full MF or shadow residual does not entail nonsoficity or nonhyperlinearity | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptFullRadicalsDoNotEntailNonsoficity` | closed |
| Opening proof step of `prop:mf-residual-calculus`, intersections of kernels are normal | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptIntersectionOfKernelsIsNormal` | closed |
| `eq:shadow-residual` `R_inf-to-2(G)` as the intersection of the `K_2(V)`, with `K_2(V)` in its printed ordinary-limit form and normal | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptShadowResidualIsIntersectionOfHSKernels` | closed |
| Sec. 3, `R_inf-to-2(G)` is normal and fully invariant | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptShadowResidualIsNormal` | closed |
| `lem:stable-finite` stable finiteness and projection comparison | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptNormMatrixCoronaStableFinite` | closed |
| `lem:kazhdan-projection-order` one-sided order for the Kazhdan projection | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptOneSidedKazhdanProjectionOrder` | closed |
| Support for `lem:kazhdan-projection-order`: one projection in `C*_max(L)`, its universal image in every target, and the literal C*-order inequality | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptMaximalCStarKazhdanProjectionOrder` | closed |
| `thm:transport` one-sided Kazhdan transport, both conjugation directions | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptOneSidedKazhdanTransport` | closed |
| Proof of `thm:transport`, both transported sequences again satisfy the bounded asymptotic-commutant hypotheses | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptOneSidedKazhdanTransportPackage` | closed |
| Proof of `thm:transport`, transport iterated along every word in the compression group | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCompressionGroupKazhdanTransport` | closed |
| `thm:transport` with arbitrary-universe ambient group and a `Type 0` Kazhdan source | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptOneSidedKazhdanTransportAnyAmbient` | closed |
| `cor:defect-hs` defect generators lie in the shadow residual | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCompressionDefectHSInvisible` | closed |
| `lem:central-corona-corner` central corona corners | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCentralCoronaCorner` | closed |
| `lem:central-corona-corner`, final clause composed as one corona-class equality over the retained subsequence | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptCornerCoronaClass` | closed |
| `thm:normal-kazhdan` normal Kazhdan radical theorem, at the printed natural-dimension radical | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptNormalKazhdanPrintedRadical` | closed |
| `thm:normal-kazhdan` again, at the basis-free radical | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptNormalKazhdanRadical` | closed |
| Support for the printed proof of `thm:normal-kazhdan`: the five corner/Kazhdan/trace/persistent-generator sentence-level steps, with the coordinate trace premise explicit | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedNormalKazhdanCornerSteps` | closed |
| Proof of `thm:normal-kazhdan`, closing sentence: every corona homomorphism kills `K` | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptNormalKazhdanCoronaVanishing` | closed |
| Proof of Theorem A, the four printed links in printed order | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedCriterionAssembly` | closed |
| Proof of Theorem A, first step: the printed defect lies in the shadow residual | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedDefectShadowInclusion` | closed |
| Proof of Theorem A, second step: normal Kazhdan subgroups of the printed defect | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedDefectNormalKazhdanRadical` | closed |
| Theorem A unfolded: such a subgroup is killed by every natural-dimension corona representation | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedDefectCoronaVanishing` | closed |
| `prop:defect-saturation` functoriality and saturation | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptDefectSaturation` | closed |
| `eq:defect-functoriality` the image inequality itself | `GroupApproximation.Manuscript.OneSidedMFRadical.map_printedDefect_to_range_le` | conditional |
| `eq:pq` `q` is nonzero at the manuscript's ring | `GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.q_ne_zero` | closed |
| `eq:matrix-compression` the unital injective endomorphism `Psi` | `GroupApproximation.LeavittFamily.matrixCompression` | conditional |
| `eq:tau` `tau = diag(X, Y)` as a unit of the twelve-by-twelve matrix ring | `GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.printedTauGL` | closed |
| `eq:whitehead-factorization` the six block-unipotent factors | `GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.tauUnit_eq_six_elementary` | closed |
| Sec. 5, `tau` belongs to the elementary group | `GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.printedTauGL_mem` | closed |
| Sec. 5, the upper-left corner has property (T) | `GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.corner_hasKazhdanPropertyT` | closed |
| Section 5, all concrete ring-and-matrix equations in printed order | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedLeavittAlgebraEquations` | closed |
| Section 5, all concrete compressor equations in printed order | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedCompressorEquations` | closed |
| Section 5, combined printed-equation fidelity package | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSectionFiveEquations` | closed |
| `eq:corner-conjugation` `tau diag(A, I) tau^-1 = diag(Psi(A), I)` | `GroupApproximation.RankTwelve.tau_fullCorner_tauInv` | conditional |
| `eq:compresses-L` `tau L tau^-1` is contained in `L` | `GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.printedDefectConfiguration` | closed |
| `prop:simple` simplicity of the rank-twelve elementary group | `GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.manuscriptPropositionSimple` | closed |
| `eq:two-sided-sandwich` every nonzero coefficient in the manuscript's exact ring has `a * x * b = 1` | `GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.coefficientRing_hasSingleSandwichDivision` | closed |
| `eq:coefficient-separation` Leavitt coefficient separation gives `a * r * b = 0` while `b * s * a * r ≠ 0` | `GroupApproximation.exists_annihilate_preserve_reverse` | conditional |
| `eq:row-unipotent-sparse`, the degenerate double commutator is exactly the square-zero unit `1 - BA` | `GroupApproximation.doubleCommutator_eq_sqZeroUnit` | conditional |
| `eq:row-unipotent-sparse`, the displayed double commutator belongs to the normal subgroup | `GroupApproximation.doubleCommutator_mem` | conditional |
| `eq:row-unipotent-dense`, the degenerate double commutator is exactly the square-zero unit `1 - BA` | `GroupApproximation.doubleCommutator_eq_sqZeroUnit` | conditional |
| `eq:row-unipotent-dense`, the displayed double commutator belongs to the normal subgroup | `GroupApproximation.doubleCommutator_mem` | conditional |
| Support for `prop:simple`: the centre of the binary Leavitt algebra is its scalar field | `GroupApproximation.BinaryLeavitt.center_eq_bot` | conditional |
| Support for `prop:simple`: every central unit over `ZMod 2` is trivial | `GroupApproximation.BinaryLeavitt.central_units_trivial` | conditional |
| Support for `prop:simple`: line-preserving conjugation extracts a nonzero elementary transvection | `GroupApproximation.exists_elGen_mem_of_conjSingle_eq` | conditional |
| Support for `prop:simple`: the inverse-entry-zero configuration extracts a nonzero elementary transvection | `GroupApproximation.exists_elGen_mem_of_inv_entry_zero` | conditional |
| Support for `prop:simple`: a noncentral matrix fails to commute with an off-diagonal single-entry matrix | `GroupApproximation.exists_noncommuting_single_of_not_central` | conditional |
| Support for `prop:simple`: the full-level relative elementary subgroup is the whole elementary group | `GroupApproximation.relativeElementary_top` | conditional |
| Support for `prop:simple`: the level-zero congruence subgroup is the centre of the full linear group | `GroupApproximation.congruenceSubgroup_bot` | conditional |
| Support for `prop:simple`: trivial central coefficient units imply a trivial full-linear-group centre | `GroupApproximation.center_eq_bot_of_central_units_trivial` | conditional |
| Support for `prop:simple`: the exact reduction from Preusser's normal-subgroup sandwich to elementary-group simplicity | `GroupApproximation.isSimpleGroup_of_preusser_sandwich` | conditional |
| `prop:defect` the explicit centralizer mark, commutator, and normal generation | `GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.manuscriptPropositionDefect` | closed |
| `eq:moved-mark` `tau c tau^-1 = e01(q) e34(1)` | `GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.tau_conj_c` | closed |
| `eq:amalgam` the amalgam `W_Q = B *_A (Q x A)` | `GroupApproximation.MFCamouflage.Camouflage` | conditional |
| Sec. 7, the projection is a split epimorphism, both vertex maps are injective, and `d` survives | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSplitPrescribedProjection` | closed |
| `prop:universal-factorization` universal factorization through the projection | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptUniversalFactorization` | closed |
| `eq:closure-pullback` MF closure pulls back, and the MF-quotient criterion for the amalgam | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrescribedQuotientRelationCalculus` | closed |
| `eq:closure-pullback`, general printed-closure identity along an MF-target-factorizing epimorphism | `GroupApproximation.Manuscript.OneSidedMFRadical.ClosurePullback.literalMFClosure_eq_comap_of_factors` | conditional |
| `eq:closure-pullback`, general MF-quotient equivalence along such an epimorphism | `GroupApproximation.Manuscript.OneSidedMFRadical.ClosurePullback.isCDEOperatorMF_quotient_iff_of_factors` | conditional |
| `eq:closure-pullback` for the camouflage projection, at the literal printed MF closure | `GroupApproximation.Manuscript.OneSidedMFRadical.ClosurePullback.camouflage_literalMFClosure_eq_comap` | conditional |
| `eq:closure-pullback` quotient equivalence for the camouflage projection | `GroupApproximation.Manuscript.OneSidedMFRadical.ClosurePullback.camouflage_isCDEOperatorMF_quotient_iff` | conditional |
| Closing prescribed-quotient paragraph, all four general closure-pullback clauses as one closed proposition | `GroupApproximation.Manuscript.OneSidedMFRadical.ClosurePullback.manuscriptMFClosurePullbackAlongFactorization` | closed |
| `prop:full-kernel-pullback`, the three printed displays for a surjection with MF-invisible kernel | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedFullKernelPullback` | closed |
| `prop:full-kernel-pullback`, the "in particular" clause for an intrinsically full kernel | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedFullKernelPullbackFromFullKernel` | closed |
| Sec. 7, image and inverse image are mutually inverse inclusion-preserving correspondences of MF-quotient kernels | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedMFQuotientCorrespondence` | closed |
| Sec. 7, the induced map on largest MF-visible quotients is an isomorphism | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedVisibleQuotientIsomorphism` | closed |
| Sec. 7, the correspondences respect composition of such surjections | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedCorrespondenceRespectsComposition` | closed |
| Sec. 7, the complete full-kernel-pullback paragraph as one closed proposition | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedFullKernelPullbackParagraph` | closed |
| `eq:one-word-quotient-test` at the visible group `Z`: the quotient is MF exactly when the relation subgroup contains `d` | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedOneWordQuotientTest` | closed |
| `eq:one-word-quotient-test`, its printed justification: every quotient of `Z` is MF and the projection kernel is the normal closure of `d` | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedOneWordQuotientJustification` | closed |
| Sec. 7 closing paragraph, the one-word test with its justification as one closed proposition | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedOneWordQuotientParagraph` | closed |
| Proof of `prop:mf-residual-calculus`, tex 193--194: "enumerate the nonidentity elements of `G/R` as `(x_j)` and enumerate the pairs in `(G/R)^2`", with the degenerate trivial branch made explicit | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptIntroEnumerateNonidentityAndPairs` | conditional |
| Proof of `prop:mf-residual-calculus`, tex 194--196: "For each `x_j`, the definition of `R` supplies a corona homomorphism whose value at `x_j` has positive distance from the identity." | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptIntroCoronaDetectorPerNonidentity` | conditional |
| Proof of `prop:mf-residual-calculus`, tex 195--196, the "positive distance from the identity" clause read as an actual C-star norm gap in a genuine norm-matrix corona | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptIntroPositiveCoronaNormDistance` | conditional |
| Proof of `prop:mf-residual-calculus`, tex 196--197: "Every such homomorphism kills `R` and therefore descends to `G/R`." | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptIntroEveryDetectorDescends` | conditional |
| Proof of `prop:mf-residual-calculus`, tex 197--198: "Choose coordinate unitary lifts, using polar correction as in Lemma `lem:central-corona-corner`." | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptIntroCoordinateUnitaryLifts` | conditional |
| Proof of `prop:mf-residual-calculus`, tex 198--203: "At stage `n`, take a direct sum of one coordinate from each of the first `n` models", with both simultaneous requirements | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptIntroExistsFiniteDiagonalStage` | conditional |
| Proof of `prop:mf-residual-calculus`, tex 201--202: "the first `n` multiplication defects are at most `1/n`" for the assembled direct sum | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptIntroDiagonalSumDefect` | conditional |
| Proof of `prop:mf-residual-calculus`, tex 202--203: "the designated value at `x_j` retains at least half of its corona-norm separation" | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptIntroDiagonalSumHalfSeparation` | conditional |
| Proof of `prop:mf-residual-calculus`, tex 203--204: "Such coordinates exist arbitrarily far out: the defects converge to zero, while the quotient norm is a limsup." | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptIntroArbitrarilyFarCoordinate` | conditional |
| Proof of `prop:mf-residual-calculus`, tex 204, the second analytic clause: the corona quotient norm is the limsup of the coordinate operator norms | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptIntroQuotientNormIsLimsup` | conditional |
| Proof of `prop:mf-residual-calculus`, tex 204--205: "The resulting operator-norm asymptotic representation detects every `x_j`" | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptIntroDiagonalEventuallySeparates` | conditional |
| Proof of `prop:mf-residual-calculus`, tex 205--206: "so its corona homomorphism is faithful on `G/R`" | `GroupApproximation.Manuscript.OneSidedMFRadical.introDiagonalCoronaHom_injective` | conditional |
| Proof of `prop:mf-residual-calculus`, tex 193--196, the printed preliminary data as a two-branch alternative for the universal MF quotient | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptIntroUniversalQuotientDiagonalAlternative` | conditional |
| Proof of `prop:mf-residual-calculus`, tex 206: "Thus `G/R` is MF", proved from the printed diagonal sum rather than from the ultraproduct route | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptIntroDiagonalRepresentationFaithful` | conditional |
| Proof of `thm:commutant`, tex 456--463, the displayed three-line commutant chain verbatim | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence100_commutantComputation` | conditional |
| Proof of `thm:commutant`, tex 464: "Thus `rho(u)^{-1} C rho(u)` is contained in `C`." | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence101_inverseConjugation_maps_commutant` | conditional |
| Proof of `lem:stable-finite`, tex 516--517: "let `(x_n)` be a bounded lift of `v`. Then `x_n^* x_n` tends to 1 in norm." | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence116_anyLift_gramDefect_tendsto` | conditional |
| Proof of `lem:stable-finite`, tex 523: "The corner is finite because `w + (1-q)` is an isometry in `A`." | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence122_cornerExtension_isometry` | conditional |
| `lem:kazhdan-projection-order` tex 530--532 together with the proof of `thm:transport` tex 599--601: the Kazhdan projection in `C*_max(L)`, the unique extension, and `P` as its image | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentences124_138_139_maximalCStarImage` | closed |
| `lem:kazhdan-projection-order` tex 530--532: "`P` in `B` is the image of the Kazhdan projection under the extension from `C*_max(L)`" | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence124_maximalCStarKazhdanProjection` | closed |
| Proof of `thm:transport`, tex 600--601: "Let `P` be the image of the Kazhdan projection", read as the image of the maximal-C-star projection rather than a substituted one | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence139_imageOfMaximalKazhdanProjection` | closed |
| Proof of `thm:transport`, tex 599--600: "Its restriction to `L` therefore extends to a star-homomorphism from `C*_max(L)`." | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence138_maximalCStarExtension` | conditional |
| Proof of `lem:kazhdan-projection-order`, tex 543--545: "Represent `B` faithfully and nondegenerately on a Hilbert space. The represented projection `P` is the orthogonal projection onto the `L`-fixed vectors." | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence126_representedKazhdanProjection_range` | conditional |
| Proof of `lem:kazhdan-projection-order`, tex 554--555: "Faithfulness of the representation gives the same projection inequality in `B`." | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence129_faithfulRepresentation_reflectsProjectionOrder` | conditional |
| Proof of `thm:transport`, tex 603--605: "This representation need not be faithful; it is used only after the following projection identity has been proved inside `B`." | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence141_identity_before_nonfaithfulRepresentation` | conditional |
| Proof of `cor:defect-hs`, tex 631--635, the displayed triple-conjugation defect limit | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence150_tripleConjugationDefect` | conditional |
| Proof of `thm:normal-kazhdan`, tex 739--745: "Taking the normalized trace on the corner", where the Hilbert--Schmidt norms use the corner's own normalized trace | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence155_cornerOwnNormalizedTrace` | conditional |
| Proof of `thm:normal-kazhdan`, tex 732--733: "in every representation of the corner there are no `K`-fixed vectors, so the defining Kazhdan inequality gives this operator inequality" | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence156_cornerKazhdanDetection` | conditional |
| Proof of `thm:normal-kazhdan`, tex 697--699: "The new `K` is a nontrivial normal property-(T) subgroup, since property (T) passes to quotients." | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence169_quotientImageRetainsNormalKazhdan` | conditional |
| Proof of `thm:normal-kazhdan`, tex 705--707: "Let `p_K` be the Kazhdan projection and `p` its image; thus `p` is the projection onto the `K`-fixed vectors in every faithful representation of the corona." | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence171_maximalProjectionImageIsFixedProjection` | conditional |
| Proof of `thm:normal-kazhdan`, tex 713--715: "the two projections have ranges `Theta(g)Fix Theta(K)` and `Fix Theta(K)`; these agree because `gKg^{-1}=K`" | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence173_conjugateProjectionRangeArgument` | conditional |
| Proof of `thm:normal-kazhdan`, tex 722--723: "In the corner `q Q_d q`, the Kazhdan projection is zero." | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence177_cornerKazhdanProjectionZero` | conditional |
| Proof of `thm:normal-kazhdan`, tex 724--733, the displayed positive element `b` and its lower bound by the Kazhdan constant squared over the Kazhdan set size, in quadratic-form reading | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence178_179_positiveAverageLowerBound` | conditional |
| Proof of `thm:normal-kazhdan`, tex 735--739: the displayed coordinate elements `b_n` as the Gram sum of the corrected corner maps | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence180_coordinateElementFormula` | conditional |
| Proof of `thm:normal-kazhdan`, tex 741--748: the displayed trace inequality, obtained from the order inequality for `b` with the printed `o(1)` loss | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence180_181_negativePartToCornerTrace` | conditional |
| Proof of `thm:normal-kazhdan`, tex 749--750: "After passing to a subsequence, one fixed `s_0` therefore stays a positive Hilbert--Schmidt distance from the corner identity." | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptSentence182_fixedElementSubsequence` | conditional |
| `prop:mf-residual-calculus` tex 176--184 and tex 208--210, the closure-operator form: extensive, monotone, idempotent, the quotient pullback, and the fixed-point criterion | `GroupApproximation.manuscriptRelationClosure` | conditional |
| Proof of `thm:headline`, tex 1071--1074: "`d` lies in the compression-centralizer defect, the defect is normal, and normal generation gives that the defect is the whole of `H`" | `GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.printedDefect_eq_top_of_configuration` | conditional |
| Proof of `prop:simple`, tex 928--931, the displayed elementary commutator relations that move source and target indices with an arbitrary coefficient | `GroupApproximation.elementaryRoot_commutator` | conditional |
| `prop:universal-factorization` tex 1216--1227 and its proof tex 1246--1249: a homomorphism killing the kernel of the surjection descends along it | `GroupApproximation.UniversalFactorization.exists_comp_eq` | conditional |
| Proof of `prop:simple`, tex 946--949: "Moreover `s_0 t_1` is nonzero, since `1=(t_0 s_0)(t_1 s_1)=t_0(s_0 t_1)s_1`", the exact printed factorization | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscript_s0_t1_factorization` | conditional |
| Proof of `prop:simple`, tex 946: "Moreover `s_0 t_1` is nonzero." | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscript_s0_mul_t1_ne_zero` | conditional |
| Proof of `prop:simple`, tex 943--944: "For every `w` there are `x,y` with `xwy=0` and `yx` nonzero. This is immediate with `x=y=1` if `w=0`." | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscript_reversing_zero_product_zero` | conditional |
| Proof of `prop:simple`, tex 945--953: "Otherwise choose `c,d` with `cwd=1` and put `x=t_1 c`, `y=d s_0`. Then `xwy=t_1 s_0=0`", with the printed contradiction for `yx` | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscript_reversing_zero_product_nonzero` | conditional |
| `eq:coefficient-separation`, tex 955--965: the four printed sandwich factorizations and the displayed definitions of `a` and `b` giving `arb=0` and `bsar` nonzero | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscript_coefficient_separation_explicit` | conditional |
| Proof of `prop:simple`, tex 967: "Now let `N` be nontrivial and choose `g` in `N` with `g` not the identity." | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscript_choose_nonidentity_normal_element` | conditional |
| Proof of `prop:simple`, tex 979--980: "Suppose next that `g` is not diagonal, and choose `l` different from `i` with the entry at `(l,i)` nonzero." | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscript_choose_nonzero_off_diagonal_entry` | conditional |
| Proof of `prop:universal-factorization`, tex 1240--1241: "Let `f` be a homomorphism from `W_Q` to `T`. Its restriction to `B` is trivial." | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscript_camouflage_restriction_to_blackHole` | conditional |
| Proof of `prop:universal-factorization`, tex 1241: "so its restriction to the amalgamated subgroup `A` is trivial" | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscript_camouflage_restriction_to_edge` | conditional |
| Sec. 5 discussion, tex 426--427: "The binary Leavitt algebra is purely infinite simple, hence an exchange ring" -- the right-exchange property at the manuscript's algebra | `GroupApproximation.BinaryLeavitt.hasRightExchange` | conditional |
| Proof of `prop:simple`, tex 935--936: "it remains to prove that every nontrivial normal subgroup of `H` contains a nonzero elementary root" | `GroupApproximation.rootDetection_of_leavittFamily` | conditional |
| Proof of `prop:mf-residual-calculus`, first printed sentence: an intersection of kernels is normal | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedIntersectionOfKernelsIsNormal` | closed |
| Proof of `prop:mf-residual-calculus`: composing a corona homomorphism with an endomorphism kills the radical, which is full invariance | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedFullInvarianceThroughComposition` | closed |
| Proof of `prop:mf-residual-calculus`: the nonidentity elements of `G/R` and the pairs in `(G/R)^2` can be enumerated | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedEnumerationsOfTheQuotient` | closed |
| Proof of `prop:mf-residual-calculus`: for each marked class the definition of the radical supplies a corona homomorphism separating it from the identity | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedCoronaDetectorAtEachMarkedClass` | closed |
| Proof of `prop:mf-residual-calculus`: every such homomorphism kills `R` and therefore descends to `G/R` | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedDetectorKillsRadicalAndDescends` | closed |
| Proof of `prop:mf-residual-calculus`: coordinate unitary lifts exist by the polar correction of `lem:central-corona-corner` | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedPolarCoordinateUnitaryLifts` | closed |
| Proof of `prop:mf-residual-calculus`: the stage-`n` direct sum is unitary, keeps the printed `1/n` multiplication defect, and retains the designated separation (the printed half, and in fact all of it) | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedStageDirectSum` | closed |
| Proof of `prop:mf-residual-calculus`: such coordinates exist arbitrarily far out, the defects converging to zero against a limsup quotient norm | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedCoordinatesExistArbitrarilyFarOut` | closed |
| Proof of `prop:mf-residual-calculus`: the resulting asymptotic representation detects every marked class, so its corona homomorphism is faithful on `G/R` and `G/R` is MF | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedQuotientDetectedAndMF` | closed |
| Proof of `prop:mf-residual-calculus`, closing sentence: the same argument applied to `G/N` is the printed closure criterion | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedClosureCriterion` | closed |
| The complete printed proof of `prop:mf-residual-calculus`, sentence by sentence, as one closed proposition | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedResidualCalculusProof` | closed |
| Printed proof of `thm:normal-kazhdan`: "in every representation of the corner there are no `K`-fixed vectors, so the defining Kazhdan inequality gives this operator inequality", in the norm form the coordinate passage consumes | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedCornerCoronaKazhdanOrder` | closed |
| Proof of `prop:simple`: "and `yx=ds_0t_1c=0` would imply" the vanishing the printed contradiction needs | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedReversedProductVanishingImplication` | closed |
| Proof of `prop:simple`: "To obtain `\eqref{eq:coefficient-separation}`, choose factorizations" | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedCoefficientSeparationFactorizations` | closed |
| Proof of `prop:simple`: the printed recipe `a=f_s x e_t c_r`, `b=d_r f_d y e_s` and the two products it forces | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedCoefficientSeparationRecipe` | closed |
| `eq:coefficient-separation`, the complete printed derivation | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedCoefficientSeparation` | closed |
| `eq:coefficient-separation` at the manuscript's own coefficient ring | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedCoefficientSeparationAtBinaryLeavitt` | closed |
| Proof of `prop:simple`: "conjugation by `g` sends `e_{ij}(a)` to `e_{ij}(y)` with `y\ne a`" | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedDiagonalConjugationMovesRoot` | closed |
| The same sentence at the manuscript's own coefficient ring | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedDiagonalConjugationMovesRootAtBinaryLeavitt` | closed |
| Proof of `prop:simple`: "the `(i,m)` entry of the defect in `\eqref{eq:row-unipotent-sparse}` is nonzero" | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedSparseDefectEntryNonzero` | closed |
| Proof of `prop:simple`: "Again `AB=0`, because its potentially nonzero coefficient contains `arb`" | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedDenseAnnihilatingProduct` | closed |
| The five printed coefficient calculations of `prop:simple` as one closed proposition | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedLeavittCoefficientCalculations` | closed |
| Sec. 7: quotienting `W_Q` by the normal closure of `d` kills the hidden vertex and the second factor | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedCamouflageQuotientKillsBothVertices` | closed |
| Sec. 7: "The resulting quotient is `Q`, with quotient map induced by `\pi_Q`" | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedCamouflageQuotientIsVisibleGroup` | closed |
| `thm:commutant`, the displayed three-line conjugation computation, in printed order | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedCommutantConjugationDisplay` | closed |
| `thm:commutant`: "Thus `\rho(u)^{-1}C\rho(u)\subseteq C`" | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedCommutantConjugationInclusion` | closed |
| `thm:commutant`, the composition step of the printed conjugation chain | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedCommutantConjugationChain` | closed |
| `thm:commutant`: "Thus `\rho(u)^{-1}C\rho(u)\subseteq C`", by the fixed-submodule route | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedCommutantConjugateInclusion` | closed |
| Proof of `lem:stable-finite`: the printed polar correction on one matrix block at the `L^2` operator norm | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedOneSidedPolarCorrection` | closed |
| Proof of `lem:stable-finite`: "Thus `v` is represented by unitaries and `vv^*=1`" | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedOneSidedUnitaryRepresentatives` | closed |
| Proof of `thm:normal-kazhdan`: "The commutation relation in the corona gives" the vanishing displacement | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedCoronaCommutationVanishing` | closed |
| Proof of `thm:normal-kazhdan`: both unitarity defects of the compressed corner converge to zero | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedBothCornerUnitarityDefects` | closed |
| Sec. 5: the binary Leavitt algebra is purely infinite simple, proved in-repo rather than cited | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedBinaryLeavittPurelyInfiniteSimple` | closed |
| Introduction: the printed `limsup` separation form of the MF model characterization, both directions | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedMFModelSeparation` | closed |
| Proof of `lem:kazhdan-projection-order`: "Represent `B` faithfully and nondegenerately on a Hilbert space" | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedFaithfulNondegenerateRepresentation` | closed |
| Proof of `thm:normal-kazhdan`: the printed coordinate elements `b_n` represent the corona element `b` | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedCoordinateGramRepresents` | closed |
| Proof of `thm:normal-kazhdan`, closing sentence: "This contradicts `s_0\in K\le D\le R_{\infty\to2}(G)`" | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedCornerFinalContradiction` | closed |
| Proof of `lem:stable-finite`: eventual invertibility of `x_n` and the `o(1)` polar distance | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedEventualInvertibilityAndPolarDistance` | closed |
| The corona quotient-norm identity: the norm of a class is the `limsup` of the coordinate norms | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedCoronaNormIsLimsup` | closed |
| Proof of `prop:mf-residual-calculus`: the printed far-out coordinate choice, retaining half the corona-norm separation | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedCoronaNormSeparation` | closed |
| The printed choice together with its printed reason, as one closed proposition | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedCoronaNormSeparationParagraph` | closed |
<!-- END-LEDGER-ROWS -->

## Known gaps inside carried rows

These are rows whose statement is carried but whose *printed proof* is not
completely reproduced.  They are listed because the per-label ledger cannot
show them: a row can be closed and unconditional while a sentence of its
printed argument has no declaration.

* ~~**`thm:normal-kazhdan`, the coordinate passage.**~~  **Now supplied.**
  `PrintedSectorProof` carries five of the six printed steps -- the corner
  Kazhdan projection vanishing in both the algebraic and the fixed-vector
  reading, the corner Kazhdan inequality `b >= (kappa^2/|S|) q`, its
  normalized-trace consequence, the persistent index as a literal strictly
  monotone subsequence, and the faithful-representation bridge
  `le_of_le_in_faithful_rep`.  The sixth, the manuscript's "the coordinate
  elements `b_n` represent `b`", is `CornerCoordinatePassage`, in two halves:

  1. **Restriction of scalars**, exactly and with no loss.  The repository's
     `IsKazhdanPair` quantifies over REAL Hilbert spaces while the corner
     representation is complex; `realifyHom` reads the latter on the same
     underlying set with the same norm, so `||pi(s) x - x||` is one real number
     read in either structure and the constant is unchanged.
  2. **Corona order to an eventual coordinate inequality**, which is the half
     that is not a triviality: at the coordinate level the corner maps form only
     an ASYMPTOTIC representation, so no Kazhdan pair applies to them directly.
     The device is `norm_filterMatrixCorona_mk_eq_limsup` -- the quotient norm
     is a limsup of coordinate norms, and a limsup below a bound is eventually
     below it.  That is the whole of the printed "with an `o(1)` loss".

  The order is transported in its norm spelling, `c <= b` iff
  `||t*1 - b|| <= t - c` for large `t`, and only the direction that follows from
  Cauchy--Schwarz is used, so no `[PartialOrder]` / `[StarOrderedRing]` instance
  is installed.  Endpoint: `eventually_printed_corner_trace_inequality`.

* **Order phrasing in the corner inequality.**  `b` is a positive element of the
  corner, not a projection, so the absorption spelling used elsewhere for
  projection order (`IsStarProjection.le_iff_mul_eq_right`) does not express
  `b >= c q`.  The instance-free reading used instead is the quadratic form,
  which is both what the printed proof produces and what the printed use
  consumes.  No order instance is installed.

## Historically withheld, now closed

* ~~**`prop:simple`, simplicity of `H = EL_12(L_F2(1,2))`.**~~
  **No longer withheld.**  The direct extraction route avoids the missing
  Preusser citation.  `rootDetection_of_leavittFamily` exhausts the diagonal,
  matching-inverse-zero, and dense-entry cases; the exact rank-twelve wrapper
  `RankTwelveEndpoint.manuscriptPropositionSimple` and the complete headline
  `manuscriptBinaryLeavittHeadline` both pass the closed audit.  The separate
  congruence-subgroup development remains a faithful conditional
  formalization of the manuscript's cited route, but is not needed for the
  closed result.
* ~~**The amenable clause of the Section 1 sterility paragraph.**~~
  **No longer withheld.**  "If `G` is amenable, its property-(T) subgroup `L`
  is finite" is cited to Bekka--de la Harpe--Valette in the manuscript and is
  now *proved* in the development:
  `Kazhdan.AmenableKazhdanFinite.finite_of_isAmenable_of_kazhdan` and
  `finite_subgroup_of_isAmenable_of_kazhdan`, packaged as the closed row
  `manuscriptAmenableKazhdanSterility`.  `Algebra.Amenable.IsAmenable` is the
  von Neumann invariant-mean definition, and the Folner extraction it needs is
  the Tarski--Hall argument in `Sofic/NearActionFolner.lean`, so this is not a
  definitional shortcut.  The manuscript's `\cite{BHV}` for this sentence is
  now decorative.
* **Property (T) for `EL_n` over a finitely generated ring** is cited to
  Ershov--Jaikin-Zapirain in the manuscript but is *not* a citation here: the
  two property-(T) rows above are proved in the development from
  `finiteFieldElementaryThree_hasKazhdanPropertyT` and the rank transport, with
  no external input.  The ledger claims the Lean proof, not the citation.

## Fidelity notes

Places where the Lean statement and the printed sentence are not word for word.
Each is a deliberate, recorded choice, and in every case the Lean statement is
at least as strong as the printed one.

* **`Comp_G(L)` is a set, not a group.**  The manuscript takes the normal
  closure of the commutators over the *set* of one-sided compressors.  The
  development also has `compressionCentralizerDefect`, which conjugates by the
  subgroup they generate.  `printedDefect` is the printed object, and
  `printedDefect_le_compressionCentralizerDefect` is the containment, which
  runs in the favourable direction: an obstruction theorem for the larger
  subgroup implies the printed one.  Every row above is stated on
  `printedDefect`.
* **`lem:kazhdan-projection-order`: read the `C*_max` carrier, not the
  surrogate.**  The printed lemma is
  `manuscriptMaximalCStarKazhdanProjectionOrder`: it constructs one projection
  in `C*_max(L)`, maps it through the universal extension to every target, and
  concludes the manuscript's literal `U* P U <= P` in any compatible C*-order.
  That is the row a reader should look at.

  The other carrier, `manuscriptOneSidedKazhdanProjectionOrder`, is a
  *surrogate* and is weaker than the print in three separate ways, recorded
  here because the status word `closed` cannot show them:

  1. it never mentions `C*_max(L)`; its projection is the spectral projection
     of a chosen finite orbit average at the isolated point `1`, and nothing
     identifies that with the image of the Kazhdan projection;
  2. the Kazhdan pair `(S, kappa)` is existentially quantified *inside* the
     conclusion, so the statement is "for some symmetric generating Kazhdan
     pair, the projection built from it satisfies ...", whereas the printed `P`
     is canonical;
  3. nothing forces that projection to be nonzero, so both absorption
     identities are satisfiable by `P = 0`.

  A fourth, pointed out by the sentence census: the Kazhdan set and constant
  are existentially quantified *inside* the conclusion, so the projection whose
  order is proved depends on that choice and no theorem says the conclusion is
  independent of it.  The printed `P` is a canonical object; the surrogate's is
  not.

  It is retained because it is the form the printed proof of `thm:transport`
  consumes, and because it needs no global order instance on the target.  It is
  not evidence for the printed lemma on its own.
* **The printed-sector package is proof support, not a second
  `thm:normal-kazhdan` endpoint.**
  `manuscriptPrintedNormalKazhdanCornerSteps` bundles the five newly attached
  corner, Kazhdan-inequality, trace, and persistent-generator implications.
  Its trace clause assumes the coordinate quadratic-form inequality; it does
  not claim the still-unformalized passage carrying the abstract corner order
  inequality through the corona quotient to those coordinate representatives.
  The theorem itself remains carried by the two normal-Kazhdan rows above.
* **`lem:stable-finite`** states the projection comparison in ring form
  (`q * p = p` for `p <= q`), for the same reason.
* **`cl_MF` has two spellings.**  `literalMFClosure` is the printed
  intersection over MF targets; `actualCoronaMFClosure` is the quotient
  pullback used elsewhere in the development.  They are equal
  (`literalMFClosure_eq_actualCoronaMFClosure`), which is why
  `eq:closure-pullback` may be carried by a statement phrased with the second.
* **`K_2(V)` uses ordinary convergence.**  The development's shadow residual is
  defined through ultrafilters; `manuscriptShadowResidualIsIntersectionOfHSKernels`
  supplies the printed ordinary-limit presentation and the identification.
* **`eq:basic-defect` and `cor:defect-hs` share a carrier.**  The introduction
  displays the corollary; there is one declaration and two rows, rather than a
  second declaration restating the first.
* **`eq:defect-functoriality` is also the first clause of the closed
  `manuscriptDefectSaturation`.**  Its own row names the standalone inequality,
  which is `conditional` only because it quantifies over `f` and `L` in front.
* **`H` is `BinaryLeavittSteinberg.ElementaryBase 12`**, which is by definition
  `elementaryGroup (Fin 12) UniversalLeavitt.BinaryLeavittAlgebra`, i.e.
  `EL_12(L_F2(1,2))`.  Universes: the analytic endpoints are stated at
  `Type 0` with `HasKazhdanPropertyT.{0,0}`, matching the manuscript's
  countable-group hypothesis.

## Auxiliary declarations

The audit file also prints, with the weaker `#audit_axioms`, the
implementation lemmas that the rows above are assembled from: the defect
generators and the bridge to `compressionCentralizerDefect`; the Leavitt
relations `p + q = 1` and `t1 q s1 = 1`; unitality, multiplicativity,
injectivity and the elementary-matrix formula for `Psi`; the matrices `X`,
`Y`, their inverse identities, the nested `tau`, and the Whitehead
factorization over an arbitrary Leavitt family; the concrete rank-twelve
compression, conjugation and commutator identities; and the amalgam's
projection and vertex injectivity.  They are not rows: a row is a printed
statement, and these are the parts.
