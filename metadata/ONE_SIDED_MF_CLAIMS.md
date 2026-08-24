# One-sided Kazhdan transport and MF radicals: current claim inventory

Source of truth: `non_mf_groups_exist.tex`, the 1,234-line manuscript headed
*One-sided Kazhdan transport and MF radicals*.

This inventory is intentionally separate from `NON_MF_PROOF_LEDGER.md`, which
states that it covers a historical 1,486-line revision. A row becomes
`closed` only after its exact manuscript endpoint has passed MSI validation
and is named by `#audit_closed_axioms` in `Audit.lean`, `PrintedAudit.lean`,
or the dedicated `RankTwelveAudit.lean`. Source code that is still compiling
is never counted.

| TeX label | Printed statement | Lean endpoint | Status |
| --- | --- | --- | --- |
| `prop:mf-residual-calculus` | MF residual calculus | `manuscriptMFResidualCalculus` | closed |
| `thm:compression-criterion` | one-sided compression criterion | `manuscriptOneSidedCompressionCriterion` plus `manuscriptPrintedDefectFiniteDimensionalSterility` | closed (two exact audited constituents) |
| `thm:headline` | the binary Leavitt group | exact full target `RankTwelveEndpoint.HeadlineConclusion`; hypothesis-free theorem-minus-simplicity `manuscriptBinaryLeavittFullRadical`; conditional full assembly `headlineConclusion_of_normalRootDetection` | open only at the printed simplicity clause; the standalone-validated hypothesis-free theorem is not full Theorem B |
| `thm:prescribed-quotients` | prescribed MF quotients | `manuscriptPrescribedMFQuotients` | closed |
| `thm:commutant` | finite-dimensional commutant rigidity | `manuscriptFiniteDimensionalCommutantRigidity` | closed |
| `lem:stable-finite` | stable finiteness of norm matrix coronas | `manuscriptNormMatrixCoronaStableFinite` | closed |
| `lem:kazhdan-projection-order` | one-sided order for the Kazhdan projection | `manuscriptOneSidedKazhdanProjectionOrder` | closed |
| `thm:transport` | one-sided Kazhdan transport | `manuscriptOneSidedKazhdanTransport`; reusable packages `manuscriptOneSidedKazhdanTransportPackage`, `manuscriptCompressionGroupKazhdanTransport`, and `manuscriptOneSidedKazhdanTransportAnyAmbient` | closed |
| `cor:defect-hs` | Hilbert--Schmidt invisibility of defect generators | `manuscriptCompressionDefectHSInvisible` | closed |
| `lem:central-corona-corner` | central corona corners | `manuscriptCentralCoronaCorner` | closed |
| `thm:normal-kazhdan` | normal Kazhdan radical theorem | `manuscriptNormalKazhdanRadical` | closed |
| `prop:defect-saturation` | defect functoriality and saturation for the exact direct-compressor defect | `manuscriptDefectSaturation` | closed |
| `prop:simple` | simplicity of `EL_12(L_F2(1,2))` | `RankTwelveEndpoint.PropositionSimple`; reductions in `RankTwelveSimplicity.lean` | open: missing normal-subgroup/root-detection theorem |
| `prop:defect` | explicit nontrivial saturating defect | `RankTwelveEndpoint.manuscriptPropositionDefect`; configuration `printedDefectConfiguration`; full-radical consequence `rankTwelve_actualCoronaMFResidual_eq_top` | closed in `RankTwelveAudit.lean` |
| `prop:universal-factorization` | universal factorization through `pi_Q` | `manuscriptUniversalFactorization` | closed |

Current closed count: **13/15**. The only open numbered statements are
`prop:simple` and `thm:headline`; the headline is blocked solely by the same
simplicity input.

## Current validation evidence

- `GroupApproximation/Endpoint/OneSidedTransportAudit.lean` has passed its
  complete endpoint audit. Its `#audit_closed_axioms` checks cover the closed
  current-manuscript endpoints and enforce the standard axiom whitelist; its
  deliberately weaker `#audit_axioms` check on `headlineConclusion_of` does
  not discharge that theorem's leading simplicity hypothesis.
- `CanonicalSector.lean` passes standalone MSI validation. Its reusable closed
  packages include `manuscriptNormalKazhdanPrintedRadical`,
  `manuscriptNormalKazhdanCoronaVanishing`,
  `manuscriptPrintedCriterionAssembly`, and
  `manuscriptPrintedDefectCoronaVanishing`. The assembly reuses the exact
  generator-by-generator shadow-containment lemma.
- `HeadlineTheorem.lean` passes standalone MSI validation.
  `manuscriptBinaryLeavittFullRadical` is hypothesis-free and proves every
  headline clause except `IsSimpleGroup H`. It must not be counted as full
  `thm:headline`; the full conclusion remains conditional on the unproved
  `NormalRootDetection` through `headlineConclusion_of_normalRootDetection`.

## Audit-closed generic routes

- `manuscriptDefectSaturation` has passed MSI and closed-axiom validation. It uses
  `printedDefect`, so functoriality ranges over individual compressors exactly
  as in the manuscript.
- `manuscriptOneSidedKazhdanProjectionOrder` and
  `manuscriptCentralCoronaCorner` pass the consolidated audit.
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
  for the existing `eq:closure-pullback` label and do not change 13/15.

## Remaining open work

The rank-12 flattening, `printedTauGL_mem`, corner property `(T)`,
`tau_compresses_corner`, `tau_conj_c`, `tau_c_commutator_ell`, and
`printedDefectConfiguration` have passed standalone MSI compilation and the
dedicated closed-axiom audit. Consequently there is no remaining
configuration or defect-saturation blocker for `thm:headline`.

The sole missing headline input is the independent simplicity proposition
`RankTwelveEndpoint.PropositionSimple`.

## Exact simplicity gap

Repository search found no derivation of simplicity for
`BinaryLeavittSteinberg.ElementaryBase 12`. The strongest nearby results are:

- `BinaryLeavitt.exists_mul_mul_eq_one`: every nonzero coefficient of the
  binary Leavitt ring admits a two-sided unit sandwich;
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

These do not imply simplicity by themselves. The missing theorem must extract
a nonzero elementary root from an arbitrary nontrivial normal subgroup. A
sufficient exact signature at the manuscript endpoint is:

```lean
∀ (N : Subgroup RankTwelveEndpoint.H) [N.Normal], N ≠ ⊥ →
  ∃ (i j : Fin 12) (hij : i ≠ j) (a : RankTwelveEndpoint.R),
    a ≠ 0 ∧ elementaryRoot i j hij a ∈ N
```

The manuscript obtains this through Preusser's normal-subgroup theorem, ring
simplicity/exchange structure, and triviality of the scalar center over
`𝔽₂`. None of that normal-structure bridge is presently formalized in the
repository. Root normal generation must not be cited as a substitute.

Displayed identities and proof steps will be added to the exhaustive proof
ledger after their owning numbered statement has an exact endpoint. This
prevents a prose-level count from disguising a missing theorem statement.
