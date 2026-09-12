# Independent review: the relative defect normalization dichotomy

Reviewer lane `reviewer`, 2026-09-12. `rdd-cocycle-prover` requested an adversarial review of `relative-defect-normalization-dichotomy` and its route `relative-defect-normalization-dichotomy-proof`, landed in 25d228dd2. It replaces the refuted splitting premise `relative-element-splits-into-m-times-centralizer`. The companion nodes `relative-normalization-modulo-kazhdan-kernel` (OPEN) and `relative-defect-via-relative-normalization` were checked for graph soundness.

## Verdict

| item | verdict |
| --- | --- |
| (1) `N_rel(σ)` is a subgroup | **PASS** |
| (2) RNORM ⟹ RDD | **PASS** |
| (3) not RNORM ⟹ not RDD (the generated group, normality, rigid pair for non-injective `σ`) | **PASS** |
| (4) the normalization-failure step | **PASS** |
| body remarks | **PASS**, one wording note on the `M = 1` case |
| graph structure | **PASS**: no false establishment |

This is an exact, elementary equivalence. It has no trust surface beyond (U) for sofic groups, namely that countable subgroups of `S_U` are sofic and that countable sofic groups admit injective trace-zero representations.

## 1. `N_rel(σ)` is a subgroup

- The permutations normalizing `σ(M)` form the normalizer subgroup of `S_U`, and `1 ∈ N_rel`.
- **Products.** `[xy, s] = x[y, s]x⁻¹ · [x, s]`. Expanding, `x y s y⁻¹ s⁻¹ x⁻¹ · x s x⁻¹ s⁻¹ = x y s y⁻¹ x⁻¹ s⁻¹`. The first factor lies in `xσ(M)x⁻¹ = σ(M)`.
- **Inverses.** `[x⁻¹, s] = x⁻¹[x, s]⁻¹x`, since `x⁻¹(s x s⁻¹ x⁻¹)x = x⁻¹ s x s⁻¹`, and it lies in `σ(M)`. Correct.

## 2. RNORM ⟹ RDD

- **The representation.** `H` is countable sofic, and `σ : H → S_U` is injective with `tr σ(h) = 0` off the identity. Such a `σ` exists for every nonprincipal `U`, by amplification.
- **`σ(z)` lies in `N_rel`.** For `z` with `[z, Γ] ⊆ M`: `σ(z)` normalizes `σ(M)` because `M ⊴ H`, and `[σ(z), σ(γ)] = σ([z, γ]) ∈ σ(M)`. So `σ(z) ∈ N_rel(σ|_G)`.
- **Applying RNORM.** `σ|_G` is a homomorphism of the pair `M ⊆ Γ ⊆ G` with `M ⊴ G`, so RNORM applies. `σ(g)σ(z)σ(g)⁻¹ ∈ N_rel` gives `σ([gzg⁻¹, γ]) ∈ σ(M)`.
- **Injectivity.** It gives `σ⁻¹(σ(M)) = M`, so `[gzg⁻¹, γ] ∈ M`. Correct.
- **Scope of RNORM used.** Only for restrictions of injective trace-zero representations. So RNORM in that restricted form already gives RDD, and then, through §3, RNORM for every homomorphism. This is the exact analogue of the Remark after Theorem 1 of `rigid-compression-defect-ladder-2026-09-11.md`.

## 3. not RNORM ⟹ not RDD

- **(4), the failure step.** If `σ(g)N_relσ(g)⁻¹ ⊆ N_rel` for every `g ∈ G`, the case `g⁻¹` gives the reverse inclusion. So a failure of normalization exhibits `g` and `x ∈ N_rel` with `σ(g)xσ(g)⁻¹ ∉ N_rel`. Correct.
- **The group `H' = <σ(G), x>`.**
  - It is countable, because Kazhdan groups are finitely generated.
  - It is sofic, as a countable subgroup of `S_U` (property (U)).
- **`σ(Γ) ⊆ σ(G)` is a rigid pair even for non-injective `σ`.**
  - Quotients of Kazhdan groups are Kazhdan.
  - `σ(P_Γ) ⊆ P_(σ(Γ))`, because `tΓt⁻¹ ⊆ Γ` implies `σ(t)σ(Γ)σ(t)⁻¹ ⊆ σ(Γ)`.
  - `σ(P_Γ)` generates `σ(G)`.
  - `σ(M)` is Kazhdan, and `σ(M) ⊆ σ(Γ)`.
- **`σ(M) ⊴ H'`.** `σ(G)` normalizes `σ(M)` because `M ⊴ G`, and `x` normalizes it by definition. Correct.
- **The defect.** `σ(g)xσ(g)⁻¹` normalizes `σ(M)`, being a product of normalizers. So its failure to lie in `N_rel` means `[σ(g)xσ(g)⁻¹, σ(γ)] ∉ σ(M)` for some `γ`. With `z' = x`, which satisfies `[x, σ(Γ)] ⊆ σ(M)`, this is a nontrivial defect modulo `M' = σ(M)` in the countable sofic `H'`. RDD fails. Correct.
- **Hypotheses of RDD match.** RDD asks for `M` normal in `H`, not only in `G`. `H'` supplies that. RNORM only needs `M ⊴ G`, which normality in `H` implies. The two quantifier shapes are compatible in both directions.

## 4. Body remarks

- **`M = 1`.** `N_rel(σ) = C_(S_U)(σ(Γ))` and RDD is `sofic-groups-kill-rigid-compression-defects`. Correct.
  - **Wording note.** "RNORM is NORM(sofic), which holds by `kun-thom-sofic-centralizer-normalization`" is slightly imprecise. Kun–Thom Theorem 4.1 is stated for sofic representations in the sense of their Definition 2.1 (`tr σ(g) = 0` for `g ≠ 1`), not for arbitrary homomorphisms. Normalization for every homomorphism follows from 4.1 through the absolute dichotomy, as in the Remark after Theorem 1 of the ladder artifact.
  - **Suggested wording:** "holds by Kun–Thom Theorem 4.1 together with `rigid-compression-defect-normalization-dichotomy`".
- **Conjugation by `σ(Γ)` preserves `N_rel`.** For `γ_0 ∈ Γ`, `[σ(γ_0)xσ(γ_0)⁻¹, σ(γ)] = σ(γ_0)[x, σ(γ_0⁻¹γγ_0)]σ(γ_0)⁻¹ ∈ σ(M)`, using `γ_0⁻¹γγ_0 ∈ Γ` and that `σ(γ_0)` normalizes `σ(M)`. More generally every non-strict compressor preserves `N_rel`. Correct.
- **Not ruled out, and not claimed.** `σ(Γ)` itself need not lie in `N_rel`, since `Γ/M` can be nonabelian. The node does not claim it does.

## 5. Graph structure

- The dichotomy's route has `requires: []` and a complete proof, so the claim is correctly established.
- `relative-defect-via-relative-normalization` targets the OPEN hinge `sofic-groups-kill-rigid-defects-modulo-kazhdan-kernels`. It requires the OPEN `relative-normalization-modulo-kazhdan-kernel`, which carries `## Attempts` and has no route of its own. So the hinge, and through it `nonsofic-hyperbolic-group`, stays OPEN. There is no false establishment.
- The route's text correctly says its premise is equivalent to its target, so the route adds formulation, not strength.
- The refuted splitting route `relative-defect-via-normalizer-split` requires the refuted premise and is inert.
