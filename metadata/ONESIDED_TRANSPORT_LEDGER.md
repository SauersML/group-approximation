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
is **not** printed with the closed macro.  Its type begins with a binder.  Six
different things put a binder there, and this ledger separates them by name
rather than by status, because the status vocabulary cannot:

* **an undischarged mathematical hypothesis.**  Two rows expose the same gap:
  the explicit simplicity reduction and `thm:headline`.  Their exact wrappers
  take `NormalRootDetection`, which has no proof in the repository; see
  *Deliberately not claimed*.
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
* **generic partial root-extraction support.**  The transvection-extraction
  theorems quantify over the ring, index type, normal subgroup, and their
  explicit matrix configurations.  They close the line-preserving and
  inverse-entry-zero configurations and detect noncentrality on a single-entry
  matrix, but do not cover the remaining dense configuration or establish
  general root detection.
* **generic congruence-subgroup support.**  The relative-elementary and
  congruence endpoints, the `GL` centre computation, and the final simplicity
  assembly quantify over the ring and index type.  The assembly retains
  Preusser's normal-subgroup sandwich as an explicit leading hypothesis; it is
  a precise reduction, not a proof of the manuscript's simplicity claim.

`MISSING` — no declaration in the development proves the row.  A `MISSING`
row's target may exist as a *statement* (a `def ... : Prop`); the gate refuses
to let it be printed in the audit under either macro, and refuses to let it
become a `theorem` without the row being updated.

Manuscript state pinned at authoring time: 1234 lines,
`sha256 0cc88f62...d8d7a778a`, 29 labelled statements.  The table has 88 rows
-- 66 `closed`, 21 `conditional`, 1 `MISSING`, naming 87 distinct declarations.
One row appears for each label, and fifty-nine further rows either split a
printed theorem into separately audited constituents or cover an unnumbered
printed sentence. One declaration appears twice, because the introduction
displays a corollary that Section 3 then states.

Among the manuscript's **15 numbered statements**, exactly **13 are closed**.
The two exceptions are `prop:simple`, whose target is `MISSING`, and full
Theorem B `thm:headline`, whose exact wrapper is `conditional` on the same
root-detection/simplicity input. The separate closed row
`manuscriptBinaryLeavittFullRadical` proves every headline clause except
simplicity and therefore does not increase the numbered-statement count.
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
| `prop:simple`, exact reduction from the missing root-detection input | `GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptBinaryLeavittSimplicityClause` | conditional |
| Theorem B `thm:headline`, every printed clause, simplicity included | `GroupApproximation.Manuscript.OneSidedMFRadical.headlineConclusion_of_normalRootDetection` | conditional |
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
| `prop:simple` simplicity of the rank-twelve elementary group | `GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint.PropositionSimple` | MISSING |
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
<!-- END-LEDGER-ROWS -->

## Known gaps inside carried rows

These are rows whose statement is carried but whose *printed proof* is not
completely reproduced.  They are listed because the per-label ledger cannot
show them: a row can be closed and unconditional while a sentence of its
printed argument has no declaration.

* **`thm:normal-kazhdan`, the coordinate passage.**  `PrintedSectorProof`
  carries five of the six printed steps -- the corner Kazhdan projection
  vanishing (both the algebraic and the fixed-vector reading), the corner
  Kazhdan inequality `b >= (kappa^2/|S|) q`, its normalized-trace consequence,
  the persistent-index selection, and the faithful-representation bridge
  `le_of_le_in_faithful_rep`.  What is NOT derived is the manuscript's sentence
  "the coordinate elements `b_n` represent `b`", i.e.

  ```text
  forall eps > 0, eventually in n, forall x,
    (kappa^2 - eps) * ||x||^2 <= sum_(s in S) ||W_n(s) x - x||^2.
  ```

  This is not a scalar-restriction triviality: at the coordinate level `W_n` is
  only an asymptotic representation, so no Kazhdan pair applies to it directly.
  It needs the corona quotient together with restriction of scalars from the
  complex corner to the real Hilbert spaces the repository's `IsKazhdanPair`
  is stated over.  The theorem itself is closed by the moving-corner route
  (`manuscriptNormalKazhdanRadical`), so this is a fidelity gap in the printed
  argument, not a hole in the result.

* **Order phrasing in the corner inequality.**  `b` is a positive element of the
  corner, not a projection, so the absorption spelling used elsewhere for
  projection order (`IsStarProjection.le_iff_mul_eq_right`) does not express
  `b >= c q`.  The instance-free reading used instead is the quadratic form,
  which is both what the printed proof produces and what the printed use
  consumes.  No order instance is installed.

## Deliberately not claimed

* **`prop:simple`, simplicity of `H = EL_12(L_F2(1,2))`.**  The manuscript
  proves it from Preusser's normal-subgroup theorem for general linear groups
  over exchange rings, together with pure infiniteness and simplicity of the
  binary Leavitt algebra and triviality of its unit-scalar center.  None of
  the decisive normal-structure bridge exists in the repository: relative
  elementary and congruence subgroups and both level endpoints are now
  formalized, but there is no theorem which assigns to every normal subgroup a
  level ideal satisfying Preusser's two sandwich inclusions.  Consequently
  there is still no unconditional `IsSimpleGroup` instance for the manuscript's
  elementary group.  The statement is kept as the named proposition
  `RankTwelveEndpoint.PropositionSimple` so that no audit can confuse it with
  what *is* proved, namely that every nonzero elementary root normally generates `H`
  (`RankTwelveEndpoint.normalClosure_defect_eq_top`).  Root normal generation
  is strictly weaker and is not a substitute.  The generic extraction module
  additionally handles the line-preserving and inverse-entry-zero
  configurations and detects noncentrality on a single-entry matrix; it
  explicitly leaves the dense all-usable-entries-nonzero configuration open,
  so it does not discharge this row.

  **One row, originally nine obligations.**  A sentence-level census
  (`metadata/ONESIDED_TRANSPORT_SENTENCE_CENSUS.md`) counted what this single
  row actually stands for.  `prop:simple`'s printed proof is five sentences
  long and each needs an object the repository does not have: pure infinite
  simplicity of `R`; the exchange property (the string "exchange ring" does not
  occur in the tree); Preusser's sandwich theorem; the `I = R` and `I = 0`
  endpoints of the case split; `Z(R) = F_2`; `z = lambda I`; `lambda` central;
  and `Z(GL_12(R)) = 1`.  The relative/congruence objects, level endpoints,
  scalar-matrix calculation, and generic conditional assembly have since been
  closed; see `CongruenceSubgroups.lean`.  The row remains missing because the
  Preusser sandwich itself has not been proved, not because those support
  declarations amount to an unconditional endpoint.
  The headline-minus-simplicity conclusions do not depend on it:
  `Rad_MF(H) = H` is a closed row above
  (`rankTwelve_actualCoronaMFResidual_eq_top`), proved through normal
  generation of the single element `d = e02(q)` rather than through simplicity.
  Triviality of every homomorphism to a countable MF group is also an
  unconditional conjunct of `manuscriptBinaryLeavittFullRadical`, derived from
  the full radical. What remains conditional is the simplicity conjunct and
  hence the full Theorem B conjunction containing it.
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
