# EX review wave 2, part 13: Toms rank theorems on block-diagonal realizers (2026-09-13)

Lane `ex-verify2-analysis`. Verdict legend as in `ex-review2-analysis-2026-09-13.md` §0. Main moved this ahead of the
census, because the ex3-rank-* lanes build on it.

**Landings reviewed** (lane ex2-rank-monotone-rounding; blobs rechecked at the live tip before landing):
- `6cc9d3a7d4`: `toms-line-subalgebra-has-no-nonconstant-continuous-rank` and its route
  `toms-line-subalgebra-no-nonconstant-rank-proof`;
- `3e87f04e9f`: `toms-simple-algebra-has-no-block-diagonal-rank-realizer` and its route
  `toms-simple-algebra-no-block-diagonal-realizer-proof`.

**Source checked:** Toms, arXiv:2606.12188v2, from the text copy in lane ex-rank-toms-b-obstruct.
- **Section 4.** `X_{i+1} = X_i × X_i × CP^{j_i}`, with `π_1, π_2` the two coordinate projections, and
  `φ_i(a) = (π_1^*a ⊗ γ_{i,1}) ⊕ (π_2^*a ⊗ γ_{i,2})`, where `γ` are line bundles from the `CP^{j_i}` factor, and
  `X_1 = Gr(d, 2d)`.
  - So `X_M = (X_n)^K × P` with `K = 2^{M−n}`, copies are coordinate projections, pushforward ranks add over copies, and
    every `X_n` is connected.
- **Lemma 2.** The point-fibre trace at `x`, followed along `x_{r+1} = (x_r, x_r, ℓ_r)` with fixed `ℓ_r`, extends to
  `τ_x`. The measure it restricts to is `δ_x`.
- **Proposition 4 and its proof.**
  - `ψ_i = ψ_i^top ⊕ ψ_i^pt`, where `ψ^pt` is a finite sum of point evaluations and `ψ^top` is the telescoped diagonal
    map on the whole `s_i`-corner.
  - `α_i = rank(s^top_{i+1})/rank(s_{i+1}) = M_i/(M_i + t_i)`, and `δ = Π α_i > 1 − η`.
  - `rank(q_m)/rank(s_m) = Π_{r<m} α_r`.

## 13.1 Verdicts

| claim | verdict |
|---|---|
| `toms-line-subalgebra-has-no-nonconstant-continuous-rank` (Theorem, Corollaries 1--2) | PASS, two wording notes |
| `toms-simple-algebra-has-no-block-diagonal-rank-realizer` | PASS, three wording notes |
| refuted `toms-diagonal-subalgebra-supports-a-nonconstant-continuous-rank` | correctly refuted. It was OPEN (`refuted_by` set), so no false establishment. |

## 13.2 The non-simple limit A (`6cc9d3a7d4`): re-derived

- **Step 1, robust Poincaré–Miranda.**
  - `u_b = min(1, dist(t, Q∖V_b)) − dist(t, V_b)` is positive exactly on `V_b`.
  - `v_b = min(u_b, t_b)` satisfies `v_b ≤ 0 < η` on `{t_b = 0}` and `v_b ≥ min(m_b, 1) > η` on `{t_b = 1}`. `Λ_b = t_b −
    1/2` behaves the same way.
  - The straight-line homotopy avoids `y = (η, …, η)` on `∂Q`, and `deg Λ = 1` because `y + 1/2 ∈ Q°`. So `v(t_η) = y`,
    which gives `t_η ∈ ∩_b V_b`.
  - A limit point `t*` has `v(t*) = 0`, and `t* ∈ V_b` forces `t*_b = 0`.
- **Step 2, budget.**
  - `d_{τ_w}(a_M) = R_M(w)/r_M`, and the pushforward of `a_n` has rank `Σ_b R_n(w^{(b)})`.
  - With `f − ε_m ≤ d(a_m) ≤ f` (an increasing limit) and `r_M = K r_n`, blockwise domination gives
    `Σ_b δ_b ≤ K r_n ε_n`.
- **Step 3, levels.** `ι_max − ι_min ≥ r_n(range_n − ε_n) ≥ 2 r_n ε_n`, and it is positive when `range_n > 0`.
  - `V_b = {κ_b(σ(t)) ≥ ι_max}` is open, since integer-valued lower semicontinuous ranks give open superlevel sets.
  - The face `{t_b = 1}` lies in `V_b` by domination at `x_max`.
- **Step 4, jump.**
  - Violators sit at `x_min` with excess `≥ 2 r_n ε_n`, so `|X| ≤ K/2`, and `X = ∅` if `ε_n = 0`.
  - Non-violators go from `≤ ι_max − 1` at `t*` to `≥ ι_max` at `t_j`. Lower semicontinuity keeps violators from
    decreasing.
- **Step 5.** Take the upper band at `σ(t_j)` and the lower band at `σ(t*)`, and let `j → ∞`. This gives
  `ε_M ≥ K/(2 r_M) = 1/(2 r_n)`.
- **Corollary 1.**
  - Barycentres `∫ τ_x dμ_M` agree with `τ` on `A_M`. `f` is continuous and affine, so `f(τ) = lim ∫ f(τ_x) dμ_M`.
  - Diagonal extensions keep `range_n ≥ c_0` for `n ≥ M_0`.
- **Corollary 2.**
  - `a_j = Σ_{i≤j} (c_i − 2/i)_+` has support inside `{a > 1/i}`, and the supports increase to `{a > 0}`.
  - In `C(Ω)`, support inclusion is Cuntz comparison.
  - `{a ≥ δ}` is compact, so it lies in some `supp a_J`. Dini on `τ(g_δ(a)) ↑ d(a)` gives uniform bands.
  - Every line lies under one copy, so line-by-line support inclusion is blockwise domination for every pair `n < M`.

**Wording notes.**
1. **The hypothesis must hold at every large `n`.**
   - The Theorem assumes block-diagonality and domination "for some `n`". Corollary 1 applies it at an `n` with
     `range_n ≥ 3ε_n`.
   - Block-diagonality passes from `n_0` to larger `n`, because coarser copies contain finer ones. Domination over the
     inherited blocks of `a_n` does not pass.
   - So read the hypothesis as holding for all `n ≥ n_0`, as the title's "from some stage on" says.
   - Corollary 2 meets the hypothesis at every `n`.
2. **Two index sets.** The sequence lives at stages `N_m`, but the Theorem writes `K = 2^{M−n}` and `r_n`. Relabel `n, M`
   as `N_n, N_M`. The bound becomes `ε_M ≥ 1/(2 r_{N_n})`, and the contradiction is unchanged.

## 13.3 The simple algebra B (`3e87f04e9f`): re-derived

- **Branch traces.**
  - `σ_x` has stage-`n` measure `β_n δ_x + κ_n`, where `κ_n` comes from paths through a point evaluation. Those paths
    land at fixed points, so `κ_n` does not depend on `x`.
  - The finite-stage measures change by at most `2(1 − α_s)` in total variation per step, and `Σ(1 − α_s) < ∞`, so they
    converge with no subnet.
  - This is Steps 1--2 of `doubling-ah-finite-stage-continuous-ranks-constant-proof`, which has PASS in
    ex-review-analysis 2026-09-12 part 4.
- **Step 3.** `d_{σ_w}(a) = β_M rank a(w)/r_M + C(a)`, and the point-block rank `Π` is constant in `w`.
- **Step 4.**
  - Domination of every block, top and point, gives `R_M ≥ P` pointwise, hence `C(a_M) ≥ C(ψ(a_n))`.
  - The bands then give `Σ_b δ_b ≤ r_M ε_n/β_M`.
- **Step 5.**
  - Top-only paths from stage 1 to `n` carry weight `Π_{i<n} α_i` and average `h` over the leaves.
  - Point paths give constants. So `f(σ_x) = δ F_n(x) + c'`, with range `δρ` over `X_n`.
  - The levels satisfy `ι_max − ι_min ≥ (r_n/β_n)(δρ − ε_n)`.
- **Step 6.** `K r_n = r_M β_n/β_M`. So the violator bound is `|X| ≤ K ε_n/(δρ − ε_n) ≤ K/2` when `δρ ≥ 3ε_n`.
- **Step 7.** `ε_M ≥ β_M K/(2 r_M) = β_n/(2 r_n) ≥ δ/(2 r_n)`, with the common constant `C(a_M)` cancelling.

**Wording notes.**
1. **Wrong justification in Step 4.** It says "`a_n ≾ a_M` gives `R_M ≥ P` pointwise".
   - Cuntz comparison in the limit only gives `d_σ(a_n) ≤ d_σ(a_M)`.
   - Pointwise `R_M ≥ P` comes from the hypothesis that every block, point blocks included, dominates its inherited
     block. The statement stands.
2. **The hypothesis must hold at every large `n`**, as in §13.2 note 1. Step 8 chooses `n` with `3ε_n ≤ δρ` after the
   fact.
3. **Missing requires.** The route has `requires: []`, but it uses Steps 1--2 of
   `doubling-ah-finite-stage-continuous-ranks-constant-proof` and Step 1 of `toms-line-subalgebra-no-nonconstant-rank-proof`.
   Add `doubling-ah-finite-stage-continuous-ranks-are-constant` and `toms-line-subalgebra-has-no-nonconstant-continuous-rank`
   to `requires`, or restate those steps.

## 13.4 What this leaves open

- Both theorems exclude realizers whose containments never move support between copies.
- Realizers with copy-dependent carries between top copies stay open in A and in B. So does
  `toms-schubert-algebra-has-a-non-constant-continuous-rank`.
- Owner notes went to ex2-rank-monotone-rounding.
