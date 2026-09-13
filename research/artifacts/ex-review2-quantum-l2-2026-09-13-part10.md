# EX review, second wave, quantum and L²: part 10. Rank locality over Bernoulli coefficients: far-site mixed differences vanish, and shape (a) never occurs

Lane `ex-verify2-quantum-l2`, 2026-09-13, at coordinator request. Index: `ex-review2-quantum-l2-2026-09-13.md`.

**Scope.**
- `bernoulli-pattern-expansions-are-finite` with its route `-proof` (lane ex3-bc-monster-shape-a, landing `59ea57d883`).
- The artifact `research/artifacts/bc-bernoulli-rank-locality-2026-09-13.md`.
- **RF.** `research/artifacts/bc-bernoulli-rank-functionals-2026-09-13.md`, Lemmas R1–R8. Its claim
  `bernoulli-assembly-injective-beyond-the-host` is PASS in ex-review2-analysis part 7 §7.3.
- **CC.** `research/artifacts/bc-bernoulli-cylinder-comparison-2026-09-13.md` §4.

**Freshness.** At tip `5a716fd85b` the claim, route, artifact, RF and predecessor blobs equal those of `59ea57d883`.

## 10.0 Verdicts

| item | verdict |
|---|---|
| Lemma L1 (a single-site change is a bounded block) | PASS |
| Lemma L2 (Combes–Thomas, no growth factor) | PASS |
| Theorem 1, steps 1–5 (uniform gap, Riesz form, integer mixed difference, estimate, integrality) | PASS |
| Corollary 2 (finite pattern expansions) | PASS |
| Corollary 3 (no shape (a); `T_r` non-surjective iff (b) or (c)) | PASS |
| Corollary 4 (uniformly gapped local operators) | PASS |
| Model tests: `G = Z` (Pimsner–Voiculescu), `Z²` component count, cylinders | PASS |
| `bernoulli-pattern-expansions-are-finite` (+ `-proof`) | **PASS**, unconditional over countable torsion-free hosts with `Z = G`, as stated. No correction needed |

**Graph.** No route requires this claim. Its only other consumer is text in the open
`bernoulli-cylinder-comparison-fails-for-some-group`. It flips no root, and `baum-connes-counterexample-group-exists`
stays OPEN.

## 10.1 Setting, re-checked

- **Covariance.** `f` acts at `δ_h` by `f(h^-1·x)`, and `u_g δ_k = δ_(kg^-1)`. Then `u_g f u_g^* δ_h = f(g^-1 h^-1 x) δ_h`,
  which is `(g·f)(h^-1 x)`. Row `h` of `f u_g` sits in column `hg`, and `d(h, hg) = ℓ(g)`.
- **Windows.**
  - `(h^-1·x)(w) = x(hw)`, so a coefficient depending on `W` reads `x|_(hW)`, and `f_g(0) = 0` kills rows with
    `x|_(hW) = 0`.
  - For finite `supp x`, only `h in supp(x) W^-1` survive, so `π_x(a)` has finite rank.
- **Density.** `f_g` is supported in `{y|_W ≠ 0}`, a compact open set missing `0`, so `f_g in C_0(X \ {0})`.
  - Locally constant functions vanishing at `0` are dense there: subtract the constant `g(0)`.
  - Symmetrizing `a` enlarges `W` to `W ∪ E^-1 W`, which keeps it configuration-local.

## 10.2 Lemma L1

1. **Block.**
   - Row `h` depends on `x_v` only if `v in hW`, that is, `h in vW^-1 ⊆ vW^-1 E = N(v)`, since `e in E`.
   - Its columns lie in `hE ⊆ N(v)`, so `Δ_v = 1_(N(v)) Δ_v 1_(N(v))`.
   - `||π_x(c)|| <= ||c||_r` gives `||Δ_v|| <= 2||a||`. At most `|W|` block rows are nonzero, so the rank is at most
     `m|W|`.
2. **Independence of the order of changes.** Suppose `v in hW` and `u in hW`. Then
   `ℓ(v^-1 u) = ℓ(w^-1 w') <= 2L_W`, by symmetry and subadditivity of `ℓ`. So for `d(u,v) > 2L_W`, the rows that see
   `v` do not see `u`, and `π_(x^(uv))(a) - π_(x^u)(a) = Δ_v`. Symmetrically the `u`-change is `Δ_u` in both columns
   of the square.

## 10.3 Lemma L2

- **Conjugation.** `e^(αψ) u_g e^(-αψ) = u_g M_g`, with `M_g = diag(e^(α(ψ(kg^-1) - ψ(k))))`.
  - `ψ = min(d(·,B), d(A,B))` is bounded and 1-Lipschitz for the left-invariant metric.
  - `d(kg^-1, k) = ℓ(g) <= L`, so `||M_g - 1|| <= e^(αL) - 1`.
- **Error.** Diagonal coefficients commute with `e^(αψ)`, so the conjugation error is
  `||Σ_(g in E) π_x(f_g) u_g (M_g - 1)|| <= K_b (e^(αL) - 1) <= 1/(2ρ)`. It is a finite sum over `E`, and no count of
  sites or volume growth enters.
- **Neumann series.** `e^(αψ)(z - π_x b) e^(-αψ) = (z - π_x b)(1 - R·err)` with `||R·err|| <= 1/2`. So
  `||e^(αψ) R e^(-αψ)|| <= 2ρ`.
- **Sandwich.** `ψ = d(A,B)` on `A` and `ψ = 0` on `B` give `||1_A R 1_B|| <= 2ρ e^(-α d(A,B))`.
- **Two resolvents.** The same `ψ` conjugates each factor, giving `4ρ^2 e^(-α d(A,B))`. This needs `b'` with the same
  `K` and `L`, which holds since both factors use `a`.

## 10.4 Theorem 1

- **Step 1: the uniform gap at every configuration.**
  - `||π_x(a) - π_x(p)|| <= ||a - p|| < 1/8` for every `x`, including `x = 0`, where `π_0` vanishes on
    `I_1 ⋊_r G`. So `spec π_x(a) ⊆ [-1/8, 1/8] ∪ [7/8, 9/8]`.
  - `P_x = χ_([1/2,∞))(π_x a)` is finite rank, and `||P_x - π_x(p)|| < 1/4`. So `rank P_x = rank π_x(p) = r_x(p)`.
  - The constants `ρ = 8/3`, `α`, `κ` and `d_0` depend on `a` only, not on `x`, `u`, `v` or the symbols. That is the
    uniformity used.
- **Step 2: Riesz form.**
  - `Γ = {|z - 1| = 1/2}` has distance `3/8` from both spectral pieces, so `||R_x|| <= 8/3`.
  - The resolvent identity gives `P_(x^v) - P_x = (1/2πi) ∮ R_(x^v) Δ_v R_x`.
  - Finite rank and trace-norm continuity let the trace pass under the integral, and the trace of a difference of
    finite-rank projections is the rank difference.
- **Step 3: the integer mixed difference as a contour integral of a trace.**
  - `M = (1/2πi) ∮ Tr(R_11 Δ_v R_01 - R_10 Δ_v R_00)`, using L1(2) for the top edge.
  - Split `R_11 Δ R_01 - R_10 Δ R_00 = (R_11 - R_10) Δ R_01 + R_10 Δ (R_01 - R_00)`.
  - Insert `R_11 - R_10 = R_11 Δ_u R_10` and `R_01 - R_00 = R_01 Δ_u R_00`.
  - The integrand becomes `Tr(R_11 Δ_u R_10 Δ_v R_01) + Tr(R_10 Δ_v R_01 Δ_u R_00)`, as printed.
- **Step 4: estimate.**
  - By cyclicity the terms are `Tr(Δ_u R_10 Δ_v R_01 R_11)` and `Tr(Δ_u R_00 R_10 Δ_v R_01)`.
  - `|Tr(XY)| <= ||X||_1 ||Y||`, with `κ = ||Δ_u||_1 <= m|W|·9/4` and the blocks cut down to `N(u)` and `N(v)`.
  - L2 with `ρ K_a (e^(αL) - 1) = (8/3)(3/16) = 1/2` bounds the terms by `κ(16/3)(9/4)(64/9) e^(-αδ)` and
    `κ(256/9)(9/4)(8/3) e^(-αδ)`.
  - The sum is `(9/4)(3072/27)κ = 256κ = C_0`. The contour length is `π`, so `|M| <= (1/2) C_0 e^(-αδ)`.
  - `δ = d(N(u), N(v)) >= d(u,v) - 2L_N`, since `ℓ(t^-1 u^-1 v t') >= ℓ(u^-1 v) - ℓ(t) - ℓ(t')`.
- **Step 5: integrality.**
  - With `d_0 = 1 + max(2L_W, 2L_N + α^-1 log C_0)` and `d(u,v) >= d_0`: `C_0 e^(-αδ) <= e^(-α) < 1`.
  - So `|M| < 1/2`, and the integer `M` is `0`.

## 10.5 Corollaries

- **Corollary 2.**
  - **Classes.** `C_0(X \ {0})` has an approximate unit of projections, since `X \ {0}` is totally disconnected and
    locally compact. That unit is also one for the crossed product, so `y = [p] - [q]`.
  - **Möbius form.** R5's inversion `n_([x]) = Σ_(U ⊆ S) (-1)^(|S \ U|) r_(x|_U)` (with `r_∅ = 0 = r_0`) is the iterated
    difference `Π_(w in S) ∂_w F(∅)`.
  - **Vanishing.** Theorem 1 at `x|_V`, `V ⊆ S \ {u,v}`, with replacement symbols `x_u` and `x_v`, gives
    `∂_u ∂_v F ≡ 0`. Differences commute, so the coefficient vanishes on any pattern with two far sites.
  - **Finitely many orbits.** Left translation puts `e` in the support and fixes diameter, balls are finite, and
    `Λ` is finite.
  - **Ranks.** By R2, `r_x(T_r n) = Σ_(t <= x) n_([t])`.
- **Corollary 3.** R8's proof, read at source (RF §2), splits `y notin im T_r` into cases.
  - An infinitely supported `n(y)` gives (a). Corollary 2 excludes it, since `n(y)` has bounded diameter, hence bounded
    size.
  - If `n(y)` is finitely supported, then `z = y - T_r(n(y))` is nonzero with all ranks `0`. R6 puts
    `y - T_r(n^(<k))` in `im K_0(I_k ⋊_r G)`, and `T_r(n^(>=k))` consists of cylinder classes with `|F| >= k`, which
    lie in `I_k`. So `z in ∩_k im K_0(I_k ⋊_r G)`, which is (b).
  - Degree 1 is (c), because the source of `T_r` is `0` there.
  - **Converse.**
    - A (b)-class `z = T_r(m)` would have `m = n(z) = 0` by R3's argument, hence `z = 0`.
    - (c) is outside the image by degree.
  - So `T_r` is non-surjective iff (b) or (c). R6's inputs (CC Lemma E and item 5) belong to the PASSED predecessor.
- **Corollary 4.**
  - `⊕_x π_x` is faithful on `C(X) ⋊_r G`. `x -> ||π_x(c)||` is lower semicontinuous, and finite-support
    configurations are dense.
  - **The gap reaches the algebra.** If `spec b` met `(γ_1, γ_2)`, a function `h` supported there would give
    `h(b) ≠ 0`. Then some finite-support `x` would have `h(π_x b) ≠ 0`, against the uniform gap.
  - `φ(0) = 0` because `γ_1 >= 0`. So `φ(b)` is a projection in `M_m(I_1 ⋊_r G)`, and Corollary 2 applies.

## 10.6 Model tests

- **`G = Z`, Pimsner–Voiculescu, re-derived.**
  - `K_1(I_1) = 0` and `K_0(I_1) = C_c(X \ {0}, Z)`, free on the cylinder indicators `1_(C_s)` (inclusion–exclusion
    removes zero conditions).
  - A shift-invariant compactly supported function must vanish on the dense finite-support configurations, which
    escape every compact set by translation. So it is `0`, and `K_1(I_1 ⋊ Z) = 0`.
  - `K_0(I_1 ⋊ Z) = coker(1 - σ) = ⊕_([s]) Z`, so `T_r` is an isomorphism. This matches CC §4.
  - No shape occurs, which is consistent with Corollary 3.
- **`Z²` component count.**
  - `S` is the boundary cycle of an `L × L` square minus the midpoints `u`, `v` of two opposite sides, at word
    distance `L`.
  - `c(S) = 2`, `c(S ∪ {u}) = c(S ∪ {v}) = 1` and `c(S ∪ {u,v}) = 1`, so the mixed difference is `1` at distance `L`.
  - By Theorem 1, `c` is the rank function of no projection over `I_1 ⋊_r G`. The Laplacian kernel on long induced
    paths has eigenvalues `2 - 2cos(π/n) -> 0`, so Corollary 4's hypothesis fails. The theorem is not vacuous.
- **Cylinders.** Occurrences `h·s <= x` read `x|_(hF_s)`. No translate of `F_s` contains two sites farther apart than
  `diam F_s`, so every such mixed difference vanishes.

## 10.7 Not re-read here

- CC Lemma E and CC item 5, used by R6. They belong to the PASSED predecessor.
- CEKN arXiv:2210.09209 and HLS; the theorem uses neither.
- Combes–Thomas (Comm. Math. Phys. 34 (1973)) and Avron–Seiler–Simon (J. Funct. Anal. 120 (1994)). Both are proved
  inline in the finite-rank form used, and the credit is correct.
- The lane's novelty check is bounded (RF, CC, the tube artifact, CEKN §§1–2; no web search).
