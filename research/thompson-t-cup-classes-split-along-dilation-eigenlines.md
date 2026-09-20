---
rg: 2
id: thompson-t-cup-classes-split-along-dilation-eigenlines
kind: claim
title: "Dilation dichotomy for (K): the cup-product classes of Thompson's T form a linear subspace K of H^2(T;R) = R^2 that is invariant under the half-rotation transfer J, and J has eigenvalue 1/2 on the Euler class and 2 on the discrete Godbillon-Vey class; so K is 0, R e_R, R gv or everything, and (K) holds iff some cup product of T is not a multiple of gv (equivalently iff some non-exact cup product vanishes on one explicit torus)"
distinct_from:
  lifted-thompson-t-euler-class-in-kahler-subspace: that is (K), e_R in K; this proves that K is a J-invariant subspace and reduces (K) to finding any cup product off the gv line, so the Godbillon-Vey component of a candidate never has to be controlled
  thompson-t-kahler-euler-class-is-a-hermitian-domination-problem: that rewrites (K) as a Hermitian domination problem for one explicit kernel; this is a symmetry statement about the whole set of realizable classes and is not about any kernel
  lifted-thompson-t-root-twist-cost-iff-euler-cup-product: that proves (K) is equivalent to the square-root twist rate on T-bar; this concerns only T and its self-similarity under the half-rotation centralizer
artifacts: []
---

**ESTABLISHED** by `thompson-t-cup-classes-split-along-dilation-eigenlines-proof`. Parts
(1)-(3) are self-contained. Parts (4) and (5) also use the literature import [GS], cited in the
proof.

**Setting.**
- `T` acts on `S^1 = R/Z` by dyadic PL homeomorphisms.
- For `f ∈ T` and `y ∈ S^1`, put `v_f(y) = (log_2 f'_-(y), log_2 f'_+(y)) ∈ Z²`.
- `det(a, b) = a_1 b_2 − a_2 b_1`.
- For an orthogonal representation `π` on a real Hilbert space and 1-cocycles `b_1, b_2` into
  `π`, the cup product is `(b_1 ∪ b_2)(g, h) = ⟨b_1(g), π(g) b_2(h)⟩`.
- `K ⊂ H²(T; R)` is the set of all classes `[b_1 ∪ b_2]`, over all `π, b_1, b_2`. Statement (K)
  is `e_R ∈ K`.

**Objects.**
- *Discrete Godbillon–Vey cocycle.* `Ω(f, g) = Σ_{y ∈ S^1} det(v_g(y), v_f(gy))`. This is a finite
  sum. Put `gv = [Ω]`.
- *Half-rotation transfer.* Let `r = (x ↦ x + 1/2)` and `C = C_T(r)`. Descent `p : C → T` is
  `p(g)(y) = 2 ĝ(y/2) mod 1`, for any lift `ĝ` of `g`. It is onto, with kernel `A = {1, r}`
  central in `C`. `i : C → T` is the inclusion. Put `J = (p^*)^{-1} ∘ i^*` on `H²(T; R)`.
- *Explicit torus.*
  - `g_0` is supported on `[1/4, 1/2]`, with pieces `[1/4, 5/16] → [1/4, 3/8]`,
    `[5/16, 3/8] → [3/8, 7/16]` and `[3/8, 1/2] → [7/16, 1/2]`.
  - `h_0` is supported on `[1/2, 3/4]`, with pieces `[1/2, 9/16] → [1/2, 5/8]`,
    `[9/16, 5/8] → [5/8, 11/16]` and `[5/8, 3/4] → [11/16, 3/4]`.
  - They commute. `σ_t` is the torus class `[g_0 | h_0] − [h_0 | g_0] ∈ H_2(T; R)`.

**Theorem.**
1. *(Structure.)* `K` is a linear subspace of `H²(T; R)`. For every endomorphism `φ` of `T`,
   `φ^* K ⊂ K`, and `J(K) ⊂ K`.
2. *(Eigenvalues.)*
   - `Ω` is a 2-cocycle.
   - `J(e_R) = e_R / 2` and `J(gv) = 2 gv`.
   - `⟨gv, σ_t⟩ = 2`, so `gv ≠ 0`.
   - `⟨e_R, τ⟩ = 0` for every torus class `τ`.
   - `J_* σ_t` is a torus class with `⟨gv, J_* σ_t⟩ = 4`. Under [GS] this gives `J_* σ_t = 2 σ_t`.
   - Exact checks of these values:
     `experiments/kahler-dilation-2026-09-17/check_gv_dilation.py`.
3. *(Projection.)* If `c ∈ K` and `c = λ e_R + μ gv`, then `λ e_R ∈ K`. Concretely,
   `2c − J(c) = (3/2) λ e_R`. A witness for it is `(π, 2b_1, b_2)` ⊕ `(π̄, −b̄_1, b̄_2)`, where
   `(π̄, b̄_i)` is `(π, b_i)` restricted to `C`, averaged over `A` onto `H^A`, and pushed down
   through `p`.
4. *(Dichotomy, using [GS]: `H²(T; R) = R e_R ⊕ R gv`, `e_R ≠ 0`.)*
   - `K` is one of `0`, `R e_R`, `R gv` or `H²(T; R)`.
   - So (K) holds iff some cup product of `T` is not a real multiple of `gv`.
   - Equivalently, (K) holds iff some non-exact cup product `c` has `⟨c, σ_t⟩ = 0`, that is
     `⟨b_1(g_0), π(g_0) b_2(h_0)⟩ = ⟨b_1(h_0), π(h_0) b_2(g_0)⟩`.
   - `gv` is not bounded, because `H²_b(T; R) = R e_b` [FFLM, Mo]. So (K) fails iff every cup
     product class of `T` is a multiple of the unbounded class `gv`.

5. *(Growth test for the gv component, using [GS].)*
   - Let `g_n, h_n ∈ C_T(x ↦ x + 2^{-n})` act on each arc `[j 2^{-n}, (j+1) 2^{-n})` by the
     `2^{-n}`-scaled copies of `g_0, h_0`.
   - For every cup product `c = [b_1 ∪ b_2] = λ e_R + μ gv` and every `n`,
     `|μ| ≤ 2^{-n-1} (‖b_1(g_n)‖ ‖b_2(h_n)‖ + ‖b_1(h_n)‖ ‖b_2(g_n)‖)`.
   - So if some non-exact cup product has `liminf_n 2^{-n}(‖b_1(g_n)‖‖b_2(h_n)‖ +
     ‖b_1(h_n)‖‖b_2(g_n)‖) = 0`, then (K) holds.
   - The `gv` line is carried only by cocycles growing at least like `2^{n/2}` on the dyadic
     towers `g_n, h_n`. That is exactly the rate of `ℓ²`-additive local cocycles: the jump
     cocycle `b(g) = Σ_y (log_2 g'_+ − log_2 g'_-)(y) δ_{gy}` into `ℓ²(Z[1/2]/Z)` has
     `‖b(g_n)‖² = 2^n ‖b(g_0)‖²`.

**Decomposition of (K) into two prerequisites that can fail independently.**
- (K1) `K ≠ 0`: `T` has some non-exact cup product in some orthogonal representation.
- (K2) `K ⊄ R gv`: not every cup product of `T` is Godbillon–Vey.
- (K) ⇔ (K1) ∧ (K2) ⇔ (K2).
- A candidate witness now needs only a nonzero pairing with the Euler eigenline `σ_e` of `J_*`.
  Its `gv` component, which the w13-w16 attempts had to cancel exactly, is irrelevant.
- (K2) fails exactly when `K = 0` or `K = R gv`. The second alternative is a concrete falsifiable
  statement: realize `gv` as a cup product, then show nothing else is realizable.

**Novelty.** The cocycle `Ω` is the Ghys–Sergiescu discrete Godbillon–Vey cocycle, up to
normalization. Its cocycle identity and its value on `σ_t` are rechecked in the proof. As far as
this graph records, the transfer `J`, its eigenvalue computation and the dichotomy are new. Not
independently reviewed.
