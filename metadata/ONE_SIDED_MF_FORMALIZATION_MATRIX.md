# Current one-sided MF manuscript: Lean formalization matrix

Scope: **only** `non_mf_groups_exist.tex` as it stands at **1056 lines** on
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
| 1 | `prop:mf-residual-calculus` | `manuscriptMFResidualCalculus : MFResidualCalculus` | `GroupApproximation/Manuscript/OneSidedMFRadical/ResidualCalculus.lean`; audit hook in `Audit.lean` | **Exact + audit-listed** |
| 2 | `thm:compression-criterion` | The three MF-radical clauses are `manuscriptOneSidedCompressionCriterion`; the arbitrary-field finite-dimensional clause is `manuscriptPrintedDefectFiniteDimensionalSterility`; `manuscriptCompleteOneSidedCompressionCriterion` packages all four. The manuscript-direct route is `manuscriptPrintedDefectShadowInclusion` followed by `manuscriptPrintedDefectNormalKazhdanRadical`. Every declaration uses the exact direct-compressor `printedDefect`. | `PrintedCriterion.lean`, `PrintedDefect.lean`, `CompressionCriterion.lean`, `PrintedDefectShadow.lean`; audit hooks in `PrintedAudit.lean` and `Audit.lean` | **Exact + audit-listed** |
| 3 | `thm:headline` | Exact target: `RankTwelveEndpoint.HeadlineConclusion`; conditional assembly is `headlineConclusion_of_configuration_and_simplicity`. Candidate declarations `printedDefectConfiguration` and `rankTwelve_actualCoronaMFResidual_eq_top` would close the literal configuration and full-radical clause, but their module is still compile-pending. Independently, `RankTwelveEndpoint.PropositionSimple` remains an actual mathematical gap. | `RankTwelveEndpoints.lean`, `RankTwelveConfiguration.lean` | **Partial / gap: compile-pending configuration plus missing simplicity** |
| 4 | `thm:prescribed-quotients` | `manuscriptPrescribedMFQuotients : PrescribedMFQuotients` | `PrescribedQuotients.lean`; audit hook in `Audit.lean` | **Exact + audit-listed** |
| 5 | `thm:commutant` | `manuscriptFiniteDimensionalCommutantRigidity : FiniteDimensionalCommutantRigidity` | `FiniteDimensionalCommutant.lean`; audit hook in `Audit.lean` | **Exact + audit-listed** |
| 6 | `lem:stable-finite` | `manuscriptNormMatrixCoronaStableFinite : NormMatrixCoronaStableFinite` | `StableFiniteness.lean`; audit hook in `Audit.lean` | **Exact + audit-listed** |
| 7 | `lem:kazhdan-projection-order` | `manuscriptOneSidedKazhdanProjectionOrder : OneSidedKazhdanProjectionOrder`. It quantifies the printed arbitrary target-algebra unitary `U` (not an ambient-group image), derives the symmetric generating Kazhdan pair from property `(T)`, and states `U⁎ P U ≤ P` as the two equivalent projection-absorption identities because a generic Lean `CStarAlgebra` has no global spectral-order instance. | `GroupApproximation/Manuscript/OneSidedMFRadical/KazhdanProjectionOrder.lean`; audit hook in `Audit.lean` | **Exact + audit-listed** |
| 8 | `thm:transport` | `manuscriptOneSidedKazhdanTransport : OneSidedKazhdanTransport` | `KazhdanTransport.lean`; audit hook in `Audit.lean` | **Exact + audit-listed** |
| 9 | `cor:defect-hs` | `manuscriptCompressionDefectHSInvisible : CompressionDefectHSInvisible` | `DefectHS.lean`; audit hook in `Audit.lean` | **Exact + audit-listed** |
| 10 | `lem:central-corona-corner` | `manuscriptCentralCoronaCorner : CentralCoronaCorner`. From the literal `rho` and nonzero commuting projection `q`, it supplies a projection lift, a strict coordinate subsequence, nonzero corner models, and the polar-corrected `cornerRepresentation`; for each `g` it pairs the corona equality `[Q_n U_n(g) Q_n]=q rho(g)` with norm convergence of the corrected corner map to that compression. | `GroupApproximation/Manuscript/OneSidedMFRadical/CentralCoronaCorner.lean`; audit hook in `Audit.lean` | **Exact + audit-listed** |
| 11 | `thm:normal-kazhdan` | `manuscriptNormalKazhdanRadical : NormalKazhdanRadical` | `NormalKazhdan.lean`; audit hook in `Audit.lean` | **Exact + audit-listed** |
| 12 | `prop:defect-saturation` | `manuscriptDefectSaturation : DefectSaturation`. Its functoriality is proved directly for individual compressors, including the literal range-subtype target `f(G)`. | `DefectSaturation.lean`; audit hook in `Audit.lean` | **Exact + audit-listed** |
| 13 | `prop:simple` | Exact unresolved proposition: `RankTwelveEndpoint.PropositionSimple := IsSimpleGroup H`. The precise missing group-theoretic implication is: for every `N ◁ H`, if `N ≠ ⊥`, then `N` contains some `elementaryRoot i j hij a` with `a ≠ 0` (equivalently, the cited normal-structure theorem must force a noncentral normal subgroup to contain a nonzero level subgroup, together with triviality of the remaining center). Once such a root is in `N`, existing root-normal-generation theorems give `N = ⊤`. No repository declaration currently proves this extraction/normal-structure step. | Statement in `RankTwelveEndpoints.lean`; nearest inputs in `Leavitt/ElementaryNormalGeneration.lean`, `Leavitt/HilbertHotelDefectNormal.lean`, and `Leavitt/LeavittSimplicity.lean` | **Gap** |
| 14 | `prop:defect` | Previously validated constituents: `c_commutes_corner`, `ell_mem_corner`, `q_ne_zero`, `defect_ne_one`, and `normalClosure_defect_eq_top`. Candidate new declarations `tau_conj_c`, `tau_c_commutator_ell`, and `printedDefectConfiguration : PrintedDefectConfiguration` supply the remaining literal group calculation, but current MSI validation is pending. | `RankTwelveEndpoints.lean`, `RankTwelveConfiguration.lean` | **Implementation present; compile pending** |
| 15 | `prop:universal-factorization` | `manuscriptUniversalFactorization : UniversalFactorization` | `UniversalFactorization.lean`; audit hook in `Audit.lean` | **Exact + audit-listed** |

Current numbered-statement accounting:

- 12 labels have exact coverage with audit-listed endpoints. Multiple audit
  commands supporting one printed theorem count as one manuscript label.
- 1 label (`prop:defect`) has a candidate exact implementation whose compile
  is pending.
- 2 labels remain partial or open: `thm:headline` and `prop:simple`; the
  headline additionally depends on the compile-pending defect configuration.

## Labeled displayed equations and constructions

| TeX label | Printed content | Lean declaration(s) | Status / exact remaining work |
|---|---|---|---|
| `eq:intrinsic-defect` | `D_G(L)` is the normal closure of `[ucu⁻¹,ℓ]` over individual `u ∈ Comp_G(L)` | `printedDefectSet`, `printedDefect`, `printedDefect_generator_mem` in `PrintedDefect.lean` | Exact definition. This is intentionally distinct from the older, larger `compressionCentralizerDefect` using `compressionGroup`. |
| `eq:leavitt` | `t_i s_j = δ_ij` and `s₀t₀+s₁t₁=1` | fields of `GroupApproximation.LeavittFamily` in `Leavitt/Leavitt.lean`; canonical instance `UniversalLeavitt.family` | Exact algebraic data. No dedicated current-manuscript closed-audit endpoint packages just this display. |
| `eq:basic-defect` | HS convergence of `V_n([ucu⁻¹,ℓ])` to `1` | `manuscriptCompressionDefectHSInvisible`; membership semantics from `mem_opToHSShadowResidual_iff` | Exact + audit-listed through `cor:defect-hs`. |
| `eq:shadow-residual` | intersection of all operator-to-HS kernels | `opToHSShadowResidual` and `mem_opToHSShadowResidual_iff` in `Sofic/OpToHSShadowResidual.lean` | Exact definition used by `DefectHS.lean` and `NormalKazhdan.lean`. |
| `eq:defect-functoriality` | `f(D_G(L)) ≤ D_{f(G)}(f(L))` | `map_printedDefect_to_range_le`; ambient-target strengthening `map_printedDefect_le` | Exact, direct-compressor proof; audit pending with `prop:defect-saturation`. |
| `eq:pq` | `p+q=1`, `t₁qs₁=1`, hence `q≠0` | `HilbertHotel.p_add_q`, `HilbertHotel.r1_mul_q_mul_s1`, `RankTwelveEndpoint.q_ne_zero` | Exact algebraic identities; no dedicated audit hook. |
| `eq:matrix-compression` | `Ψ(A)=qI₃+s₀At₀`, multiplicative, unital, injective | `LeavittFamily.matrixCompression` and its algebraic lemmas in `Leavitt/LeavittCorner.lean`; consumed by `RankTwelve.shift_halfCorner_shiftInv` | Core algebra exists. The matrix-to-literal-group transport is part of the remaining rank-12 configuration work. |
| `eq:tau` | `τ=diag(X,Y)` in `GL₁₂(R)` | Validated raw definitions `RankTwelve.tau`, `tauInv`, `tauUnit`, and `RankTwelveEndpoint.printedTauGL`; candidate elementary-group membership `printedTauGL_mem` | Raw matrix/unit exact. Literal membership in `EL₁₂` is **compile pending**. |
| `eq:whitehead-factorization` | six block-unipotent factors for `diag(X,X⁻¹)` | Validated nested identity `RankTwelve.tau_eq_whitehead_product`; candidate lift chain `tauUnit_eq_six_elementary`, `flat12Units_elementary_mem`, `printedTauGL_mem` | Nested identity exact; literal `EL₁₂` lift is **compile pending**. |
| `eq:corner-conjugation` | `τ diag(A,I₉) τ⁻¹ = diag(Ψ(A),I₉)` | Validated nested identities `RankTwelve.tau_fullCorner_tauInv` and `shift_halfCorner_shiftInv`; candidate literal transport `tau_conj_corner_elementaryRoot` / `tau_compresses_corner` | Nested matrix statement exact; literal group transport is **compile pending**. |
| `eq:compresses-L` | `τLτ⁻¹ ≤ L` | candidate `RankTwelveEndpoint.tau_compresses_corner`; candidate package `printedDefectConfiguration` | **Implementation present; compile pending.** |
| `eq:moved-mark` | `τcτ⁻¹=e₀₁(q)e₃₄(1)` | candidate `RankTwelveEndpoint.tau_conj_c`; candidate resulting commutator `tau_c_commutator_ell` | **Implementation present; compile pending.** |
| `eq:amalgam` | `W_Q=B *_A (Q×A)` | `MFCamouflage.Camouflage`, `Edge`, `blackHole`, and `productVertex`; packaged behavior in `manuscriptSplitPrescribedProjection` | Exact construction and vertex-map facts. The split-projection package itself is not currently audit-listed. |
| `eq:closure-pullback` | MF closure is pulled back along `π_Q` | `manuscriptPrescribedQuotientRelationCalculus : PrescribedQuotientRelationCalculus` | Exact endpoint, including the quotient-MF equivalence and `N=π⁻¹π(N)` clause; audit pending. |

## Essential unlabelled displayed proof data

These displays are used materially in proofs even though the TeX source does
not attach an equation label to each of them.

| Manuscript display / fact | Lean declaration(s) | Status |
|---|---|---|
| `X` and `Y` and the identities `XY=YX=I₆` | `RankTwelve.shift`, `shiftInv`, `shift_mul_shiftInv`, `shiftInv_mul_shift` | Exact algebraic support. |
| The upper-left `EL₃(R)` subgroup `L≤H` | validated definitions `RankTwelveEndpoint.cornerRootSet`, `corner`; candidate realization `cornerEmbedding`, `cornerEmbedding_range` | Subgroup definition exact; literal `EL₃` realization is compile pending. |
| Property `(T)` for `H=EL₁₂(R)` and for the corner `L` | validated `RankTwelveEndpoint.hasKazhdanPropertyT`; candidate `corner_hasKazhdanPropertyT` | Ambient result exact; corner transport is compile pending. |
| `c=e₃₄(1)` centralizes `L`, and `ℓ=e₁₂(1)` lies in `L` | `RankTwelveEndpoint.c_commutes_corner`, `ell_mem_corner` | Exact declarations; these are two closed fields needed by `prop:defect`. |
| `d=e₀₂(q)≠1` and `⟪d⟩ᴴ=H` | `RankTwelveEndpoint.defect`, `defect_ne_one`, `normalClosure_defect_eq_top` | Exact. Normal generation is proved directly and does not depend on the still-missing simplicity theorem. |
| Every printed defect generator is HS-shadow invisible, hence the whole printed defect is | `manuscriptCompressionDefectHSInvisible`; direct closed endpoint `manuscriptPrintedDefectShadowInclusion` | Exact + audit-listed in `Audit.lean`. |
| A full MF radical kills maps to MF targets | `manuscriptFullRadicalKillsMFTargets : FullRadicalKillsMFTargets` | Exact + audit-listed in `PrintedAudit.lean`. |
| The split map `π_Q`, its section, injective vertex maps, and survival of `d` in `W_Q` | `manuscriptSplitPrescribedProjection : SplitPrescribedProjection` | Exact endpoint; audit pending. |

## Remaining work that blocks “everything formalized”

1. Formalize the cited normal-subgroup input needed for
   `RankTwelveEndpoint.PropositionSimple` and prove `IsSimpleGroup H`.
   A sufficient exact missing theorem is
   `∀ (N : Subgroup H) [N.Normal], N ≠ ⊥ →
   ∃ i j (hij : i ≠ j) a, a ≠ 0 ∧ elementaryRoot i j hij a ∈ N`.
   The closest existing declarations are:
   `BinaryLeavitt.exists_mul_mul_eq_one` (every nonzero ring coefficient has a
   unit sandwich),
   `elementaryGroup_normal_eq_top_of_elementaryRoot_mem` (a normal subgroup
   containing a sandwiched root is top), and
   `HilbertHotel.normalClosure_elementaryRoot_eq_top` (every nonzero root
   normally generates at rank at least five). None extracts a root from an
   arbitrary nontrivial normal subgroup.
2. Complete MSI validation of `RankTwelveConfiguration.lean`, then use the
   resulting `printedDefectConfiguration` with
   `headlineConclusion_of_configuration_and_simplicity` to close
   `thm:headline`.
3. Add a closed-axiom audit hook for the finished rank-12 defect declaration
   after its module passes MSI. The unnumbered prescribed relation-calculus
   endpoint also remains outside the consolidated audit.

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
`elementaryGroup_normal_eq_top_of_elementaryRoot_mem` starts only *after* a
root has been placed in `N`.

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

Once stages 1 and 2 exist, the final proof uses repository declarations that
already exist:

- `RankTwelveEndpoint.nontrivial : Nontrivial H`;
- `HilbertHotel.normalClosure_elementaryRoot_eq_top` from
  `GroupApproximation/Leavitt/HilbertHotelDefectNormal.lean`, instantiated
  with `n = 12` and the extracted `a ≠ 0`;
- alternatively,
  `elementaryGroup_normal_eq_top_of_elementaryRoot_mem` from
  `GroupApproximation/Leavitt/ElementaryNormalGeneration.lean`, with the unit
  sandwich supplied by `BinaryLeavitt.exists_mul_mul_eq_one`.

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

Only the bottom normal-generation arrow is currently formalized.  The two
upper inputs are the exact remaining mathematical work.
