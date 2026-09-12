# One-sided Kazhdan transport and MF radicals: current claim inventory

Source of truth: `non_mf_groups_exist.tex`, the 1,234-line manuscript headed
*One-sided Kazhdan transport and MF radicals*.

This inventory is intentionally separate from `NON_MF_PROOF_LEDGER.md`, which
states that it covers a historical 1,486-line revision. A row becomes
`closed` only after its exact manuscript endpoint has passed MSI validation
and is named by `#audit_closed_axioms` in `Audit.lean`, `PrintedAudit.lean`,
`RankTwelveAudit.lean`, or `Endpoint/OneSidedTransportAudit.lean`. Source code
that is still compiling is never counted.

| TeX label | Printed statement | Lean endpoint | Status |
| --- | --- | --- | --- |
| `prop:mf-residual-calculus` | MF residual calculus | `manuscriptMFResidualCalculus` | closed |
| `thm:compression-criterion` | one-sided compression criterion | `manuscriptOneSidedCompressionCriterion` plus `manuscriptPrintedDefectFiniteDimensionalSterility` | closed (two exact audited constituents) |
| `thm:headline` | the binary Leavitt group | `manuscriptBinaryLeavittHeadline : RankTwelveEndpoint.HeadlineConclusion` | closed, including simplicity |
| `thm:prescribed-quotients` | prescribed MF quotients | `manuscriptPrescribedMFQuotients` | closed |
| `thm:commutant` | finite-dimensional commutant rigidity | `manuscriptFiniteDimensionalCommutantRigidity` | closed |
| `lem:stable-finite` | stable finiteness of norm matrix coronas | `manuscriptNormMatrixCoronaStableFinite` | closed |
| `lem:kazhdan-projection-order` | one-sided order for the Kazhdan projection | **printed carrier:** `manuscriptMaximalCStarKazhdanProjectionOrder` (projection in `C*_max(L)`, universal image in every target, literal `U* P U <= P`). **Surrogate:** `manuscriptOneSidedKazhdanProjectionOrder` — projection built from an existentially quantified Kazhdan pair, order as two absorption identities; its conclusion is satisfiable with `P = 0`, so it is not by itself the printed lemma | closed; read the printed carrier, not the surrogate |
| `thm:transport` | one-sided Kazhdan transport | `manuscriptOneSidedKazhdanTransport`; reusable packages `manuscriptOneSidedKazhdanTransportPackage`, `manuscriptCompressionGroupKazhdanTransport`, and `manuscriptOneSidedKazhdanTransportAnyAmbient` | closed |
| `cor:defect-hs` | Hilbert--Schmidt invisibility of defect generators | `manuscriptCompressionDefectHSInvisible` | closed |
| `lem:central-corona-corner` | central corona corners | `manuscriptCentralCoronaCorner` | closed |
| `thm:normal-kazhdan` | normal Kazhdan radical theorem | `manuscriptNormalKazhdanPrintedRadical` at the printed natural-dimension radical; `manuscriptNormalKazhdanRadical` at the basis-free one | closed |
| `prop:defect-saturation` | defect functoriality and saturation for the exact direct-compressor defect | `manuscriptDefectSaturation` | closed |
| `prop:simple` | simplicity of `EL_12(L_F2(1,2))` | `RankTwelveEndpoint.manuscriptPropositionSimple : PropositionSimple` | closed in the endpoint audit |
| `prop:defect` | explicit nontrivial saturating defect | `RankTwelveEndpoint.manuscriptPropositionDefect`; configuration `printedDefectConfiguration`; full-radical consequence `rankTwelve_actualCoronaMFResidual_eq_top` | closed in `RankTwelveAudit.lean` |
| `prop:universal-factorization` | universal factorization through `pi_Q` | `manuscriptUniversalFactorization` | closed |

Current closed count: **15/15**. Every numbered statement has an exact closed
endpoint.

## Current validation evidence

- `GroupApproximation/Endpoint/OneSidedTransportAudit.lean` has passed its
  complete endpoint audit. Its `#audit_closed_axioms` checks cover the closed
  current-manuscript endpoints and enforce the standard axiom whitelist,
  including `manuscriptPropositionSimple` and
  `manuscriptBinaryLeavittHeadline`.
- `CanonicalSector.lean` passes standalone MSI validation. Its reusable closed
  packages include `manuscriptNormalKazhdanPrintedRadical`,
  `manuscriptNormalKazhdanCoronaVanishing`,
  `manuscriptPrintedCriterionAssembly`, and
  `manuscriptPrintedDefectCoronaVanishing`. The assembly reuses the exact
  generator-by-generator shadow-containment lemma.
- `HeadlineTheorem.lean` passes standalone MSI validation.
  `manuscriptBinaryLeavittHeadline` is the hypothesis-free full Theorem B;
  `manuscriptBinaryLeavittFullRadical` remains the independently useful package
  of every headline clause except simplicity.
- `CountableNonMF.lean` packages the hypothesis-free abstract consequences:
  existence of a countable non-MF group, the negation of universal countable
  MF-ness, the equivalent `IsOperatorMF` version, the countable Kazhdan
  full-radical witness, and the general saturated-defect consequence.  The
  full simple headline is supplied separately by `manuscriptBinaryLeavittHeadline`.
- `PrintedDefinitions.lean` closes the Introduction's corona-denominator,
  unitary-model, and corona-image/MF-target descriptions without restating the
  already audited MF-radical identities. `PrintedRemarks.lean` packages the
  finite-dimensional commutant caveat, the finite-subgroup sterility chain,
  the sofic/hyperlinear scope separation, and normality of intersections of
  kernels. These are supporting prose rows; the numbered count remains 15/15.

## Audit-closed generic routes

- `manuscriptDefectSaturation` has passed MSI and closed-axiom validation. It uses
  `printedDefect`, so functoriality ranges over individual compressors exactly
  as in the manuscript.
- `manuscriptOneSidedKazhdanProjectionOrder` and
  `manuscriptCentralCoronaCorner` pass the consolidated audit.
- `CornerCoronaClass.lean` composes the two index-set-dependent conclusions of
  `manuscriptCentralCoronaCorner` into the printed final corona-class equality
  over the retained subsequence. Its closed wrapper is exported and listed in
  the endpoint audit; it refines the existing lemma row and does not change
  the 15/15 count.
- The MF part and the arbitrary-field finite-dimensional part of
  `thm:compression-criterion` are separately exact and audit-listed. The
  convenience conjunction `manuscriptCompleteOneSidedCompressionCriterion`
  also passes the consolidated audit.
- `PrintedDefectShadow.lean` contains the manuscript-direct route from
  generator HS invisibility to the whole printed defect and then through the
  normal-Kazhdan theorem. Both closed wrapper propositions pass the audit.
- `LiteralMFClosure.lean` identifies the printed intersection-of-kernels MF
  closure with the generic quotient-pullback closure. Its literal
  residual-calculus endpoint uses the same functoriality, quotient-MF, closure,
  and trivial-radical APIs as `manuscriptMFResidualCalculus`; the two closed
  propositions remain separate because their quotient subgroups occur in
  dependent types.
- `ShadowResidual.lean` supplies the ordinary-limit `K₂(V)` presentation,
  its identification with the ultrafilter shadow residual, and generic
  normality. `PrintedDefectShadow.lean` uses those generic shadow facts but
  retains the manuscript's generator-by-generator route from
  `manuscriptCompressionDefectHSInvisible`; its audited wrapper does not pass
  through the larger `compressionGroup` defect.
- `RankTwelveAudit.lean` validates all eight exact declarations needed for
  `prop:defect`, including `manuscriptPropositionDefect` and the consequent
  equality `rankTwelve_actualCoronaMFResidual_eq_top`. Each uses only the
  repository's standard audited axioms.
- `LeavittMarkNontrivial.lean` supplies the generic `eq:pq` chain from
  `t₁ p₁ s₁ = 1` to `p₁ ≠ 0` and nontriviality of the associated
  elementary generator; `RankTwelveCorner.lean` upgrades the canonical corner
  map to an isomorphism `EL₃(R) ≃* corner`. Both live modules are exported by
  `GroupApproximation.lean` and feed the rank-12 manuscript construction.
- `ClosurePullback.lean` supplies the literal MF-closure pullback and quotient
  equivalence for a general MF-target-factorizing epimorphism, specializes
  them to the camouflage projection, and packages the four printed clauses as
  `manuscriptMFClosurePullbackAlongFactorization`. These are supporting rows
  for the existing `eq:closure-pullback` label and do not change 15/15.

## Closed simplicity and headline

The rank-12 flattening, `printedTauGL_mem`, corner property `(T)`,
`tau_compresses_corner`, `tau_conj_c`, `tau_c_commutator_ell`, and
`printedDefectConfiguration` have passed standalone MSI compilation and the
dedicated closed-axiom audit. There is no remaining configuration,
defect-saturation, or simplicity blocker for `thm:headline`.

`RankTwelveEndpoint.manuscriptPropositionSimple` proves the exact simplicity
proposition, and `manuscriptBinaryLeavittHeadline` packages the complete
headline unconditionally.

## Direct simplicity proof

The closed derivation of simplicity for
`BinaryLeavittSteinberg.ElementaryBase 12` uses the following chain:

- `BinaryLeavitt.exists_mul_mul_eq_one`: every nonzero coefficient of the
  binary Leavitt ring admits a two-sided unit sandwich;
- `BinaryLeavitt.center_eq_bot` and `BinaryLeavitt.central_units_trivial`:
  the coefficient-ring centre is the base field and its units over `𝔽₂` are
  trivial;
- `elementaryGroup_normal_eq_top_of_elementaryRoot_mem`: a normal subgroup
  containing a sandwiched elementary root is the whole elementary group;
- `HilbertHotel.normalClosure_elementaryRoot_eq_top`: at rank at least five,
  every nonzero elementary root normally generates the whole elementary group;
- `RankTwelveEndpoint.normal_eq_top_of_nonzero_elementaryRoot_mem`: the
  preceding result specialized to an arbitrary normal subgroup of the exact
  rank-twelve group;
- `RankTwelveEndpoint.properNormal_inf_elementaryRootSubgroup_eq_bot`: every
  proper normal subgroup meets each elementary root subgroup trivially;
- `RankTwelveEndpoint.elementaryRoot_mem_center_iff`: no nontrivial elementary
  root is central; and
- `RankTwelveEndpoint.isSimpleGroup_of_normal_root_detection`: the exact
  reduction from root detection to `IsSimpleGroup H`.
- `ElementarySimplicity.normal_eq_top_of_colMatrix_mem` and
  `normal_eq_top_of_double_commutator`: a normal subgroup is all of `EL_ι(R)`
  once it contains a suitable nontrivial single-column perturbation, and the
  latter theorem produces one from a double commutator under explicit scalar
  vanishing/nonvanishing hypotheses;
- `ElementarySimplicity.center_elementaryGroup_eq_bot`: the elementary-group
  centre is trivial under the already isolated “central units are trivial”
  coefficient hypothesis; and
- `ElementarySimplicity.RootDetection` with
  `isSimpleGroup_of_rootDetection`: the generic root-detection predicate and
  its exact reduction to simplicity.
- `exists_elGen_mem_of_conjSingle_eq`: a line-preserving conjugation
  configuration produces a nonzero elementary transvection in the normal
  subgroup;
- `exists_elGen_mem_of_inv_entry_zero`: an off-diagonal entry which is nonzero
  in `g` and zero in `g⁻¹` produces a nonzero elementary transvection by a
  double commutator and row extraction; and
- `exists_noncommuting_single_of_not_central`: matrix noncentrality is already
  detected on an off-diagonal single-entry matrix.
- `relativeElementary_top` and `congruenceSubgroup_bot`: the two endpoint
  calculations `ELₙ(R,R) = ELₙ(R)` and `Cₙ(R,0) = Z(GLₙ(R))` used in
  the manuscript's level-ideal case split;
- `center_eq_bot_of_central_units_trivial`: trivial central coefficient units
  force the centre of the full linear group to be trivial; and
- `isSimpleGroup_of_preusser_sandwich`: the complete generic assembly from an
  explicitly supplied Preusser sandwich theorem to elementary-group
  simplicity.

`ElementaryTransvectionExtraction.lean` now contains a source-level closure of
the previously open usable dense-entry configuration.  In that case,
`exists_annihilate_preserve_reverse` uses the Leavitt relations to kill the
obstruction while retaining a nonzero reversed coefficient, and
`exists_elGen_mem_of_dense_entries` completes the row extraction.
`DiagonalNormalExtraction.rootDetection_of_leavittFamily` then proves the
exhaustive case split: diagonal elements use the centre calculation, while a
nonzero off-diagonal `g_{li}` is handled according as the matching inverse
entry is zero or nonzero.  This unconditional endpoint and its exact
rank-twelve wrapper have passed MSI and the closed endpoint audit.  The independent
`CongruenceSubgroups.lean` route continues to expose the Preusser sandwich as
an explicit hypothesis.

```lean
∀ (N : Subgroup RankTwelveEndpoint.H) [N.Normal], N ≠ ⊥ →
  ∃ (i j : Fin 12) (hij : i ≠ j) (a : RankTwelveEndpoint.R),
    a ≠ 0 ∧ elementaryRoot i j hij a ∈ N
```

The manuscript obtains this through Preusser's normal-subgroup theorem.  The
formalization instead uses Leavitt coefficient separation and the
matching-entry case split described above.  The exact root-detection theorem,
simplicity wrapper, and full headline have passed the closed audit, giving the
strict count 15/15.

Displayed identities and proof steps will be added to the exhaustive proof
ledger after their owning numbered statement has an exact endpoint. This
prevents a prose-level count from disguising a missing theorem statement.
