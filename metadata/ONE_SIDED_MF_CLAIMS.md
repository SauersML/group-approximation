# One-sided Kazhdan transport and MF radicals: current claim inventory

Source of truth: `non_mf_groups_exist.tex`, the 1,056-line manuscript headed
*One-sided Kazhdan transport and MF radicals*.

This inventory is intentionally separate from `NON_MF_PROOF_LEDGER.md`, which
states that it covers a historical 1,486-line revision. A row becomes
`closed` only after its exact manuscript endpoint has passed MSI validation
and is named by `#audit_closed_axioms` in `Audit.lean` or the dedicated
`PrintedAudit.lean`. Source code that is still compiling is never counted.

| TeX label | Printed statement | Lean endpoint | Status |
| --- | --- | --- | --- |
| `prop:mf-residual-calculus` | MF residual calculus | `manuscriptMFResidualCalculus` | closed |
| `thm:compression-criterion` | one-sided compression criterion | `manuscriptOneSidedCompressionCriterion` plus `manuscriptPrintedDefectFiniteDimensionalSterility` | closed (two exact audited constituents) |
| `thm:headline` | the binary Leavitt group | `RankTwelveEndpoint.HeadlineConclusion`; conditional `headlineConclusion_of_configuration_and_simplicity` | open: simplicity gap; rank-12 configuration compile pending |
| `thm:prescribed-quotients` | prescribed MF quotients | `manuscriptPrescribedMFQuotients` | closed |
| `thm:commutant` | finite-dimensional commutant rigidity | `manuscriptFiniteDimensionalCommutantRigidity` | closed |
| `lem:stable-finite` | stable finiteness of norm matrix coronas | `manuscriptNormMatrixCoronaStableFinite` | closed |
| `lem:kazhdan-projection-order` | one-sided order for the Kazhdan projection | `manuscriptOneSidedKazhdanProjectionOrder` | closed |
| `thm:transport` | one-sided Kazhdan transport | `manuscriptOneSidedKazhdanTransport` | closed |
| `cor:defect-hs` | Hilbert--Schmidt invisibility of defect generators | `manuscriptCompressionDefectHSInvisible` | closed |
| `lem:central-corona-corner` | central corona corners | `manuscriptCentralCoronaCorner` | closed |
| `thm:normal-kazhdan` | normal Kazhdan radical theorem | `manuscriptNormalKazhdanRadical` | closed |
| `prop:defect-saturation` | defect functoriality and saturation for the exact direct-compressor defect | `manuscriptDefectSaturation` | closed |
| `prop:simple` | simplicity of `EL_12(L_F2(1,2))` | `RankTwelveEndpoint.PropositionSimple`; reductions in `RankTwelveSimplicity.lean` | open: missing normal-subgroup/root-detection theorem |
| `prop:defect` | explicit nontrivial saturating defect | candidate `RankTwelveEndpoint.printedDefectConfiguration` and constituent theorems | compile pending; not closed |
| `prop:universal-factorization` | universal factorization through `pi_Q` | `manuscriptUniversalFactorization` | closed |

Current closed count: **12/15**.

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

## Explicitly compile-pending work

The following source declarations are candidates, not closure claims:

- the rank-12 flattening, `printedTauGL_mem`, corner property `(T)`,
  `tau_compresses_corner`, `tau_conj_c`, `tau_c_commutator_ell`, and
  `printedDefectConfiguration` in `RankTwelveConfiguration.lean`.

Even if the rank-12 configuration compiles, `thm:headline` remains open until
the independent simplicity input `RankTwelveEndpoint.PropositionSimple` is
proved and audited.

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
