# Current one-sided MF manuscript: Lean formalization matrix

Scope: **only** `non_mf_groups_exist.tex` as it stands at **1234 lines** on
2026-08-24.  This matrix does not describe the older 1486-line revision and
does not inherit closure claims from `NON_MF_PROOF_LEDGER.md` or
`NON_MF_SENTENCE_CENSUS.md`.

The manuscript contains 15 numbered mathematical statements.  Status terms
used below are deliberately strict:

- **Exact + audit-listed**: an endpoint matching the current printed statement
  exists, and a `#audit_closed_axioms` command naming it exists in the current
  manuscript audit files.  This records the source-level audit hook; this
  matrix is not itself a build log.
- **Exact; audit pending**: an exact endpoint has passed MSI compilation, but
  its `#audit_closed_axioms` command has not yet been successfully validated
  (the command may already be present in `Audit.lean`).
- **Implementation present; compile pending**: source declarations intended to
  prove the printed claim are present, but the current MSI validation has not
  yet succeeded or been reported.  This is not counted as closure.
- **Partial / gap**: supporting declarations exist, but the complete printed
  statement has no unconditional exact endpoint.  Such a row is not counted
  as closed.

Unless a fully qualified name is shown, declarations are in
`GroupApproximation.Manuscript.OneSidedMFRadical`.

## The 15 numbered statements

| # | TeX label | Exact Lean endpoint or gap | File | Status |
|---:|---|---|---|---|
| 1 | `prop:mf-residual-calculus` | `manuscriptMFResidualCalculus : MFResidualCalculus`; the literal intersection-of-kernels version is `manuscriptMFResidualCalculusLiteral`, using `literalMFClosure_eq_actualCoronaMFClosure` and the same generic residual APIs. The wrappers are kept separate because quotienting by propositionally equal subgroups changes a dependent quotient type. | `GroupApproximation/Manuscript/OneSidedMFRadical/ResidualCalculus.lean`, `LiteralMFClosure.lean`; audit hooks in `Audit.lean` | **Exact + audit-listed** |
| 2 | `thm:compression-criterion` | The three MF-radical clauses are `manuscriptOneSidedCompressionCriterion`; the arbitrary-field finite-dimensional clause is `manuscriptPrintedDefectFiniteDimensionalSterility`; `manuscriptCompleteOneSidedCompressionCriterion` packages all four. The manuscript-direct route is `manuscriptPrintedDefectShadowInclusion` followed by `manuscriptPrintedDefectNormalKazhdanRadical`; `manuscriptPrintedCriterionAssembly` is the standalone-validated link-by-link package. The proof uses `manuscriptCompressionDefectHSInvisible` generator by generator and shadow-residual normality, without enlarging to the `compressionGroup` defect. | `PrintedCriterion.lean`, `PrintedDefect.lean`, `CompressionCriterion.lean`, `PrintedDefectShadow.lean`, `CanonicalSector.lean`; closed audit in `Endpoint/OneSidedTransportAudit.lean` | **Exact + audit-closed** |
| 3 | `thm:headline` | Exact full target: `RankTwelveEndpoint.HeadlineConclusion`. `manuscriptBinaryLeavittFullRadical : BinaryLeavittFullRadical` is standalone-validated and hypothesis-free: it proves countability, nontriviality, property `(T)`, both full-radical equalities, triviality of maps to countable MF groups, and non-MF-ness, but deliberately omits simplicity. The full assembly `headlineConclusion_of_normalRootDetection` remains conditional on the unproved `NormalRootDetection`; equivalently, `RankTwelveEndpoint.PropositionSimple` is the sole missing clause. | `RankTwelveEndpoints.lean`, `RankTwelveConfiguration.lean`, `RankTwelveAudit.lean`, `RankTwelveSimplicity.lean`, `HeadlineTheorem.lean` | **Partial / gap: hypothesis-free headline minus simplicity verified; full Theorem B open** |
| 4 | `thm:prescribed-quotients` | `manuscriptPrescribedMFQuotients : PrescribedMFQuotients` | `PrescribedQuotients.lean`; audit hook in `Audit.lean` | **Exact + audit-listed** |
| 5 | `thm:commutant` | `manuscriptFiniteDimensionalCommutantRigidity : FiniteDimensionalCommutantRigidity` | `FiniteDimensionalCommutant.lean`; audit hook in `Audit.lean` | **Exact + audit-listed** |
| 6 | `lem:stable-finite` | `manuscriptNormMatrixCoronaStableFinite : NormMatrixCoronaStableFinite` | `StableFiniteness.lean`; audit hook in `Audit.lean` | **Exact + audit-listed** |
| 7 | `lem:kazhdan-projection-order` | `manuscriptOneSidedKazhdanProjectionOrder : OneSidedKazhdanProjectionOrder`. It quantifies the printed arbitrary target-algebra unitary `U` (not an ambient-group image), derives the symmetric generating Kazhdan pair from property `(T)`, and states `U⁎ P U ≤ P` as the two equivalent projection-absorption identities because a generic Lean `CStarAlgebra` has no global spectral-order instance. | `GroupApproximation/Manuscript/OneSidedMFRadical/KazhdanProjectionOrder.lean`; audit hook in `Audit.lean` | **Exact + audit-listed** |
| 8 | `thm:transport` | `manuscriptOneSidedKazhdanTransport : OneSidedKazhdanTransport`; `TransportAssembly.lean` adds the closed reusable-hypotheses package, compression-group iteration, and arbitrary-ambient-universe form as `manuscriptOneSidedKazhdanTransportPackage`, `manuscriptCompressionGroupKazhdanTransport`, and `manuscriptOneSidedKazhdanTransportAnyAmbient` | `KazhdanTransport.lean`, `TransportAssembly.lean`; successfully checked by `Endpoint/OneSidedTransportAudit.lean` | **Exact + audit-closed** |
| 9 | `cor:defect-hs` | `manuscriptCompressionDefectHSInvisible : CompressionDefectHSInvisible` | `DefectHS.lean`; audit hook in `Audit.lean` | **Exact + audit-listed** |
| 10 | `lem:central-corona-corner` | `manuscriptCentralCoronaCorner : CentralCoronaCorner`. From the literal `rho` and nonzero commuting projection `q`, it supplies a projection lift, a strict coordinate subsequence, nonzero corner models, and the polar-corrected `cornerRepresentation`; for each `g` it pairs the corona equality `[Q_n U_n(g) Q_n]=q rho(g)` with norm convergence of the corrected corner map to that compression. | `GroupApproximation/Manuscript/OneSidedMFRadical/CentralCoronaCorner.lean`; audit hook in `Audit.lean` | **Exact + audit-listed** |
| 11 | `thm:normal-kazhdan` | `manuscriptNormalKazhdanRadical : NormalKazhdanRadical` | `NormalKazhdan.lean`; audit hook in `Audit.lean` | **Exact + audit-listed** |
| 12 | `prop:defect-saturation` | `manuscriptDefectSaturation : DefectSaturation`. Its functoriality is proved directly for individual compressors, including the literal range-subtype target `f(G)`. | `DefectSaturation.lean`; audit hook in `Audit.lean` | **Exact + audit-listed** |
| 13 | `prop:simple` | Exact unresolved proposition: `RankTwelveEndpoint.PropositionSimple := IsSimpleGroup H`. `RankTwelveSimplicity.lean` closes every step after root detection: `normal_eq_top_of_nonzero_elementaryRoot_mem`, `properNormal_inf_elementaryRootSubgroup_eq_bot`, `elementaryRoot_mem_center_iff`, and the exact reduction `isSimpleGroup_of_normal_root_detection`. The remaining theorem must extract a nonzero elementary root from every nontrivial normal subgroup (or prove the central-or-root dichotomy and eliminate the scalar center branch). | Statement in `RankTwelveEndpoints.lean`; closed reductions in `RankTwelveSimplicity.lean`; normal-generation inputs in `Leavitt/ElementaryNormalGeneration.lean` and `Leavitt/HilbertHotelDefectNormal.lean` | **Gap: root detection / center branch** |
| 14 | `prop:defect` | `RankTwelveEndpoint.manuscriptPropositionDefect : PropositionDefect` is the exact unconditional endpoint. `printedDefectConfiguration` supplies the literal compressor and commutator package, while `rankTwelve_actualCoronaMFResidual_eq_top` records its full-radical consequence. All eight constituent/endpoint declarations in `RankTwelveAudit.lean` pass the closed-axiom audit. | `RankTwelveEndpoints.lean`, `RankTwelveConfiguration.lean`, `RankTwelveAudit.lean` | **Exact + audit-listed** |
| 15 | `prop:universal-factorization` | `manuscriptUniversalFactorization : UniversalFactorization` | `UniversalFactorization.lean`; audit hook in `Audit.lean` | **Exact + audit-listed** |

Current numbered-statement accounting:

- 13 labels have exact coverage with audit-listed endpoints. Multiple audit
  commands supporting one printed theorem count as one manuscript label.
- 2 labels remain partial or open: `thm:headline` and `prop:simple`; the
  headline is blocked solely by the same missing simplicity theorem.

Validation note: `Endpoint/OneSidedTransportAudit.lean` has passed as a whole.
`CanonicalSector.lean` and `HeadlineTheorem.lean` also pass standalone MSI
validation. Standalone validation of `manuscriptBinaryLeavittFullRadical`
does not change the count because its proposition explicitly omits the
simplicity conjunct of full Theorem B.

## Labeled displayed equations and constructions

| TeX label | Printed content | Lean declaration(s) | Status / exact remaining work |
|---|---|---|---|
| `eq:intrinsic-defect` | `D_G(L)` is the normal closure of `[ucu⁻¹,ℓ]` over individual `u ∈ Comp_G(L)` | `printedDefectSet`, `printedDefect`, `printedDefect_generator_mem` in `PrintedDefect.lean` | Exact definition. This is intentionally distinct from the older, larger `compressionCentralizerDefect` using `compressionGroup`. |
| `eq:leavitt` | `t_i s_j = δ_ij` and `s₀t₀+s₁t₁=1` | fields of `GroupApproximation.LeavittFamily` in `Leavitt/Leavitt.lean`; canonical instance `UniversalLeavitt.family` | Exact algebraic data. No dedicated current-manuscript closed-audit endpoint packages just this display. |
| `eq:basic-defect` | HS convergence of `V_n([ucu⁻¹,ℓ])` to `1` | `manuscriptCompressionDefectHSInvisible`; membership semantics from `mem_opToHSShadowResidual_iff` | Exact + audit-listed through `cor:defect-hs`. |
| `eq:shadow-residual` | intersection of all operator-to-HS kernels | `hsKernel`, `mem_hsKernel_iff`, `opToHSShadowResidual_eq_iInf_hsKernel`, and closed endpoint `manuscriptShadowResidualIsIntersectionOfHSKernels` in `ShadowResidual.lean` | Exact ordinary-limit `K₂(V)` presentation and generic residual identification; audit hook in `Audit.lean`. |
| `eq:defect-functoriality` | `f(D_G(L)) ≤ D_{f(G)}(f(L))` | `map_printedDefect_to_range_le`; ambient-target strengthening `map_printedDefect_le`; package `manuscriptDefectSaturation` | Exact + audit-listed, with direct individual-compressor proof. |
| `eq:pq` | `p+q=1`, `t₁qs₁=1`, hence `q≠0` | generic `LeavittFamily.p0_add_p1`, `t1_mul_p1_mul_s1`, and `p1_ne_zero` in `LeavittMarkNontrivial.lean`; rank-specific `RankTwelveEndpoint.q_ne_zero` | Exact generic algebraic chain, consumed by the audited rank-12 defect endpoint. |
| `eq:matrix-compression` | `Ψ(A)=qI₃+s₀At₀`, multiplicative, unital, injective | `LeavittFamily.matrixCompression` and its algebraic lemmas in `Leavitt/LeavittCorner.lean`; consumed by `RankTwelve.shift_halfCorner_shiftInv` and the verified literal transport in `RankTwelveConfiguration.lean` | Exact algebra and exact rank-12 transport. |
| `eq:tau` | `τ=diag(X,Y)` in `GL₁₂(R)` | `RankTwelve.tau`, `tauInv`, `tauUnit`, `RankTwelveEndpoint.printedTauGL`, and audited membership theorem `printedTauGL_mem` | Exact; literal membership in `EL₁₂` is audit-closed. |
| `eq:whitehead-factorization` | six block-unipotent factors for `diag(X,X⁻¹)` | `RankTwelve.tau_eq_whitehead_product`, `tauUnit_eq_six_elementary`, `flat12Units_elementary_mem`, `printedTauGL_mem` | Exact factorization and exact audited `EL₁₂` lift. |
| `eq:corner-conjugation` | `τ diag(A,I₉) τ⁻¹ = diag(Ψ(A),I₉)` | `RankTwelve.tau_fullCorner_tauInv`, `shift_halfCorner_shiftInv`, `tau_conj_corner_elementaryRoot`, and `tau_compresses_corner` | Exact nested matrix identity and literal group transport. |
| `eq:compresses-L` | `τLτ⁻¹ ≤ L` | `RankTwelveEndpoint.tau_compresses_corner`; package `printedDefectConfiguration` | Exact; package audit-closed. |
| `eq:moved-mark` | `τcτ⁻¹=e₀₁(q)e₃₄(1)` | `RankTwelveEndpoint.tau_conj_c`; resulting commutator `tau_c_commutator_ell` | Exact; commutator endpoint audit-closed. |
| `eq:amalgam` | `W_Q=B *_A (Q×A)` | `MFCamouflage.Camouflage`, `Edge`, `blackHole`, and `productVertex`; packaged behavior in `manuscriptSplitPrescribedProjection` | Exact construction and vertex-map facts. The split-projection package itself is not currently audit-listed. |
| `eq:closure-pullback` | MF closure is pulled back along `π_Q` | Existing camouflage endpoint `manuscriptPrescribedQuotientRelationCalculus`; literal general theorem `ClosurePullback.literalMFClosure_eq_comap_of_factors`; quotient equivalence `ClosurePullback.isCDEOperatorMF_quotient_iff_of_factors`; camouflage specializations; closed four-clause package `ClosurePullback.manuscriptMFClosurePullbackAlongFactorization` | Exact at both the general factorizing-epimorphism level and the printed camouflage instance; new audit hooks added, validation pending. |

## Essential unlabelled displayed proof data

These displays are used materially in proofs even though the TeX source does
not attach an equation label to each of them.

| Manuscript display / fact | Lean declaration(s) | Status |
|---|---|---|
| `X` and `Y` and the identities `XY=YX=I₆` | `RankTwelve.shift`, `shiftInv`, `shift_mul_shiftInv`, `shiftInv_mul_shift` | Exact algebraic support. |
| The upper-left `EL₃(R)` subgroup `L≤H` | `RankTwelveEndpoint.cornerRootSet`, `corner`, `cornerEmbedding`, and `cornerEmbedding_range`; faithful-copy theorem `cornerEmbedding_injective` and equivalence `cornerEquiv` in `Leavitt/RankTwelveCorner.lean` | Exact canonical corner and exact isomorphism with `EL₃(R)`. |
| Property `(T)` for `H=EL₁₂(R)` and for the corner `L` | `RankTwelveEndpoint.hasKazhdanPropertyT`; audited `corner_hasKazhdanPropertyT` | Exact ambient and corner results. |
| `c=e₃₄(1)` centralizes `L`, and `ℓ=e₁₂(1)` lies in `L` | `RankTwelveEndpoint.c_commutes_corner`, `ell_mem_corner` | Exact declarations; these are two closed fields needed by `prop:defect`. |
| `d=e₀₂(q)≠1` and `⟪d⟩ᴴ=H` | `RankTwelveEndpoint.defect`, `defect_ne_one`, `normalClosure_defect_eq_top` | Exact. Normal generation is proved directly and does not depend on the still-missing simplicity theorem. |
| Every printed defect generator is HS-shadow invisible, hence the whole printed defect is | `manuscriptCompressionDefectHSInvisible`; direct closed endpoint `manuscriptPrintedDefectShadowInclusion` | Exact + audit-listed in `Audit.lean`. |
| The canonical-sector proof assembled link by link | `manuscriptNormalKazhdanPrintedRadical`, `manuscriptNormalKazhdanCoronaVanishing`, `manuscriptPrintedCriterionAssembly`, `manuscriptPrintedDefectCoronaVanishing` | Exact packages; `CanonicalSector.lean` passes standalone MSI validation. The defect containment reuses the direct generator-by-generator lemma. |
| Every headline conclusion except simplicity | `manuscriptBinaryLeavittFullRadical : BinaryLeavittFullRadical` | Hypothesis-free and standalone MSI-validated, but intentionally not counted as full `thm:headline`. |
| A full MF radical kills maps to MF targets | `manuscriptFullRadicalKillsMFTargets : FullRadicalKillsMFTargets` | Exact + audit-listed in `PrintedAudit.lean`. |
| The split map `π_Q`, its section, injective vertex maps, and survival of `d` in `W_Q` | `manuscriptSplitPrescribedProjection : SplitPrescribedProjection` | Exact endpoint; audit pending. |

## Remaining work that blocks “everything formalized”

1. Formalize the cited normal-subgroup input needed for
   `RankTwelveEndpoint.PropositionSimple` and prove `IsSimpleGroup H`.
   A sufficient exact missing theorem is
   `∀ (N : Subgroup H) [N.Normal], N ≠ ⊥ →
   ∃ i j (hij : i ≠ j) a, a ≠ 0 ∧ elementaryRoot i j hij a ∈ N`.
   The closed reductions are:
   `BinaryLeavitt.exists_mul_mul_eq_one` (every nonzero ring coefficient has a
   unit sandwich),
   `RankTwelveEndpoint.normal_eq_top_of_nonzero_elementaryRoot_mem`,
   `RankTwelveEndpoint.properNormal_inf_elementaryRootSubgroup_eq_bot`, and
   `RankTwelveEndpoint.isSimpleGroup_of_normal_root_detection`.
   None extracts a root from an arbitrary nontrivial normal subgroup.
2. Apply the resulting `RankTwelveEndpoint.PropositionSimple` to the already
   verified `headlineConclusion_of_configuration_and_simplicity` and
   `printedDefectConfiguration` to close `thm:headline`. The unnumbered
   prescribed relation-calculus endpoint remains outside the consolidated
   audit.

No theorem about the older rank-16 Hilbert-hotel model is counted as closure
of a current rank-12 manuscript statement.

## Actionable Lean roadmap for `prop:simple`

This section is planning documentation.  The declarations under **Missing**
are proposed theorem shapes, not existing conditional endpoints, and none is
counted in the table above.

Write

```lean
open RankTwelveEndpoint
-- R = UniversalLeavitt.BinaryLeavittAlgebra
-- H = BinaryLeavittSteinberg.ElementaryBase 12
```

### 1. Normal structure: isolate the scalar exceptional branch

The useful form of the cited Preusser input is not unconditional root
extraction: a normal subgroup can first fall into the level-zero central
branch.  The exact missing dichotomy should therefore have the shape

```lean
-- Missing: not currently declared in the repository.
theorem normal_le_center_or_contains_nonzero_root
    (N : Subgroup H) [N.Normal] :
    N ≤ Subgroup.center H ∨
      ∃ (i j : Fin 12) (hij : i ≠ j) (a : R),
        a ≠ 0 ∧ elementaryRoot i j hij a ∈ N
```

This is the minimal endpoint needed downstream.  A closer transcription of
the paper may instead define the level ideal of `N` and prove the two
Preusser inclusions

```text
EL₁₂(R, level(N)) ≤ N ≤ C₁₂(R, level(N)).
```

The repository currently has no definition/theorem implementing that normal
structure for `elementaryGroup`.  In particular,
`RankTwelveEndpoint.normal_eq_top_of_nonzero_elementaryRoot_mem` starts only
*after* a root has been placed in `N`.

The ring-side theorem already available for simplifying a nonzero level is

```lean
GroupApproximation.BinaryLeavitt.exists_mul_mul_eq_one
```

from `GroupApproximation/Leavitt/LeavittSimplicity.lean`: every nonzero
coefficient `a : R` admits `u * a * v = 1`.  It supplies the simple-ring/unit-
sandwich algebra, but not the group normal-structure dichotomy.

### 2. Eliminate the center/scalar branch over `𝔽₂`

The central branch requires two missing facts.  First, commuting with all
elementary roots must force a central element of `H` to be a scalar matrix.
Second, the scalar must come from the center of the binary Leavitt ring, which
the manuscript identifies with `𝔽₂`; its only nonzero scalar is `1`.
The closed theorem `RankTwelveEndpoint.elementaryRoot_mem_center_iff` proves
the strictly weaker fact that no nontrivial elementary root is central; it
does not classify an arbitrary central matrix.
A compact final endpoint is

```lean
-- Missing: not currently declared in the repository.
theorem rankTwelve_center_eq_bot : Subgroup.center H = ⊥
```

An auditable decomposition of that endpoint would use the following theorem
shapes:

```lean
-- Missing matrix-centralizer calculation.
theorem central_element_is_scalar
    (z : H) (hz : z ∈ Subgroup.center H) :
    ∃ λ : R,
      ((z : (Matrix (Fin 12) (Fin 12) R)ˣ) :
          Matrix (Fin 12) (Fin 12) R) = Matrix.scalar (Fin 12) λ

-- Missing center computation for the universal binary Leavitt ring.
theorem binaryLeavitt_center_is_base_scalar
    (z : R) (hz : ∀ a : R, Commute z a) :
    ∃ λ : ZMod 2, algebraMap (ZMod 2) R λ = z
```

The precise coercion used for the matrix value may be adjusted to the
existing `elementaryGroup` subtype API; the mathematical content must remain
the displayed scalar assertion.  The proof then uses invertibility of `z`
to rule out `λ = 0` and the two-element field calculation to get `λ = 1`,
hence `z = 1` and `Subgroup.center H = ⊥`.

Repository search found no theorem computing the center of
`UniversalLeavitt.BinaryLeavittAlgebra` and no theorem computing the center of
this elementary group.  `UniversalLeavitt.BinaryLeavittAlgebra` is verified
to be the specialization
`BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)` in
`GroupApproximation/Leavitt/UniversalLeavitt.lean`; that is the existing base-
field identification to use.

### 3. Close every normal subgroup using existing root normal generation

Once root detection exists, the final proof is already packaged by:

- `RankTwelveEndpoint.nontrivial : Nontrivial H`;
- `RankTwelveEndpoint.normal_eq_top_of_nonzero_elementaryRoot_mem`; and
- `RankTwelveEndpoint.isSimpleGroup_of_normal_root_detection`.

The closure argument should be:

1. Let `N ◁ H`.
2. Apply `normal_le_center_or_contains_nonzero_root N`.
3. In the central case, rewrite `rankTwelve_center_eq_bot`; then `N = ⊥`.
4. In the root case, use
   `HilbertHotel.normalClosure_elementaryRoot_eq_top (n := 12) (by omega)
   i j hij ha`.
5. Normality of `N` and root membership give
   `Subgroup.normalClosure {elementaryRoot i j hij a} ≤ N`; rewriting the
   preceding normal-closure theorem gives `N = ⊤`.
6. Package the dichotomy with `RankTwelveEndpoint.nontrivial` as
   `IsSimpleGroup H`, thereby proving `RankTwelveEndpoint.PropositionSimple`.

The logical dependency is therefore

```text
Preusser central-or-root dichotomy
              +
rankTwelve_center_eq_bot
              |
              v
nontrivial normal N contains a nonzero root
              |
              v
HilbertHotel.normalClosure_elementaryRoot_eq_top
              |
              v
       IsSimpleGroup H
```

The normal-generation and final packaging arrows are formalized.  Root
detection remains the exact missing mathematical input; the manuscript's
Preusser route decomposes it through the central-or-root dichotomy and the
full center computation.
