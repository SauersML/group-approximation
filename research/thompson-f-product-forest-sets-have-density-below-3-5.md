---
rg: 2
id: thompson-f-product-forest-sets-have-density-below-3-5
kind: claim
title: Product-form forest window sets in Thompson's group F have large-window density strictly below 3.5, and 3.5 is their exact supremum, so Belk-Brown's value is the ceiling of the whole product class
distinct_from:
  thompson-f-product-forest-vectors-stay-below-71-72: that caps weighted product vectors by the Rayleigh bound 4 * 71/72 = 3.944 through Bhattacharyya overlaps; this caps 0/1 product sets (density, not Rayleigh quotient of a weighted vector) at 3.5 through min-overlaps, allows arbitrary shape-dependent sets rather than size-only split weights, and shows 3.5 is sharp.
  thompson-f-guba-q4-systems-have-common-multiples: that turns density above 4 - 2/k into solutions of Guba's Q_k; this shows that no product forest set family reaches density 3.5 in the large-window limit, so the densities needed for Q_5 (above 3.6), and Guba's own 3.5004, cannot come from this class.
  thompson-f-one-sided-forest-windows-are-norm-lossless: that shows the window support loses nothing for the norm; this shows that the product amplitude class restricted to indicators loses exactly down to 3.5 for density.
  thompson-f-is-amenable: that is the open root; this kills one explicit class of density certificates and decides nothing about the root.
artifacts:
  - experiments/thompson-f-product-set-density-2026-09-17/check_density_formula.py
  - experiments/thompson-f-product-set-density-2026-09-17/check_density_formula_n6.out
  - experiments/thompson-f-product-set-density-2026-09-17/opt_indicator_cap.py
  - experiments/thompson-f-product-set-density-2026-09-17/opt_indicator_cap_N5_40.out
  - experiments/thompson-f-product-set-density-2026-09-17/finite_n_opt.py
  - experiments/thompson-f-product-set-density-2026-09-17/finite_n_opt_n4_20.out
---

**ESTABLISHED (pen and paper; the counting identity is also checked by brute force in exact
arithmetic).** Notation of `thompson-f-norm-bound-from-forest-renewal-test-vector-proof`, steps 1–2:
`G = <s_0, s_1> ≅ F`, `S_n` the pointed forests `(T_0, ..., T_{m-1}; i)` with `n` leaves, and
`E : S_n -> G` the injective window embedding. For a finite `Y ⊂ F`, `δ(Y)` is its average induced
degree in the Cayley graph for `{x_0^±1, x_1^±1}` (Guba's density; `δ̄ = sup δ = 4` iff `F` is
amenable).

**The class.** A *product forest family* is:
- a truncation `N >= 1`;
- sets `𝒜_s` (bulk trees) and `ℬ_s` (pointer trees) of binary trees with `s` leaves, `1 <= s <= N`,
  with no trees of more than `N` leaves;
- the single leaf in `𝒜`, and `ℬ` nonempty.

Its window sets are `Y_n = E{(T_0..T_{m-1}; i) in S_n : T_i ∈ ℬ, and T_j ∈ 𝒜 for j != i}`. These are
the indicator members of the w13 product ansatz (pointer-tree factor times bulk-tree factors), with
arbitrary shape-dependent sets in place of size-only split weights.

**Theorem.**
1. **Exact formula.** For every `n`, `δ(Y_n) = 2 (Sh_n + Mg_n) / D_n`, where
   `D_n = sum_s b_s Y_{n-s}`, `Sh_n = sum_{s,t} x_s x_t Y_{n-s-t}`, and `Mg_n = sum_m e_m Y_{n-m}`.
   - `a_s = |𝒜_s|`, `b_s = |ℬ_s|`, `x_s = |𝒜_s ∩ ℬ_s|`, and `e_m` is the number of `T = (L, R) ∈ ℬ_m`
     with `L ∈ ℬ` and `R ∈ 𝒜`.
   - `W` is the renewal sequence of `a` (`W_0 = 1`, `W_l = sum_s a_s W_{l-s}`), and `Y = W * W`.
2. **Limit.** Let `R ∈ (0, 1]` solve `sum_s a_s R^s = 1`, and put `Q = sum_s b_s R^s`. Then
   `δ_∞ := lim_n δ(Y_n) = 2 [ (sum_s x_s R^s)^2 + sum_m e_m R^m ] / Q`.
3. **Cap.** Let `η_s = a_s R^s` and `ν_s = b_s R^s / Q`, two probability vectors on `{1..N}`, with
   cdf `F` of `ν`. Let `t` be the least integer with `F(t) >= 1/2`, and put `α = F(t-1) < 1/2`. Then
   `δ_∞ <= 2 Ψ(ν, η) <= 3 + 2α^2 < 3.5`, where
   `Ψ = max_u [sum_s min(u η_s, ν_s / u)]^2 + sum_m min(ν_m, (ν * η)_m)`.
4. **Sharpness.** Let `𝒜 = ℬ = 𝒟_k`, the trees of depth `<= k` (`N = 2^k`). Then `δ_∞ = 4 - 2R_k`,
   where `R_k` is the root in `(1/4, 1)` of `D_k(R) = 1`, with `D_0(x) = x` and
   `D_k(x) = x + D_{k-1}(x)^2`. Moreover `R_k` decreases strictly to `1/4`.
   - Values: `4 - 2R_k = 2.7639, 3.0319, 3.1674, 3.2481, 3.3012` for `k = 1..5`, and `3.4474` at
     `k = 14`.

So the supremum of `δ_∞` over all product forest families is exactly `3.5`, and no family attains it.

Proof route: `thompson-f-product-forest-sets-have-density-below-3-5-proof`.

**What dies.**
- *Class:* density certificates built as product forest window sets, in the large-window
  (renewal) limit. This covers every choice of the two tree sets, of any shapes and any truncation.
- *Invariant:* the renewal-tilted size laws `ν` (pointer tree) and `η` (bulk tree), together
  with the fact that under the uniform measure on `Y_n` the pointer and its right neighbour have
  independent sizes in the limit.
- *Step where every member dies:* the median `t` of `ν`.
  - A merge edge needs the merged tree, of size `X + Y` with `X ~ ν` and `Y ~ η` independent, to be
    a pointer tree. Below `t` the merged sizes carry mass at most `α G(t-1)`, and above `t` the
    pointer trees carry mass at most `1/2`.
  - A shift edge needs both trees in `𝒜 ∩ ℬ`. Its overlap `max_u sum min(u η, ν/u)` is capped by
    splitting at the same `t`.
  - Together these give `Ψ <= 3/2 + α^2`.
- *Consequences.*
  - The value `3.5` reported by Belk–Brown is the exact ceiling of the product class. The
    depth-`<= k` family reaches it only in the limit. (We read their sets as bounded-depth forest
    sets of this kind but do not quote their construction here, so the identification is a remark,
    not an input to the theorem.)
  - Guba's `δ̄ > 3.5` (sets of density about `3.5004`) and any finite set for `Q_5` (density
    `> 3.6`) cannot be large windows of a product family. They need membership of the pointer tree
    correlated with that of its neighbours. This is the set-level form of the "comonotone"
    survivor recorded (as a heuristic) in `thompson-f-product-forest-vectors-stay-below-71-72`.
  - Indicators lose against weights inside the same product ansatz. Weighted product vectors reach
    Rayleigh value `> 4 · 0.9743 = 3.897` (`thompson-f-norm-bound-from-log-scale-forest-limit`), but
    0/1 amplitudes stop at `3.5`, because `min(p, q)` replaces `sqrt(p q)` in both overlaps.

**Scope and what is not proved.**
- The theorem is about `lim_n δ(Y_n)`. It does not bound `δ(Y_n)` at finite `n`.
  - At finite `n` the weight `Y_{n-s-t}` need not factor, and a log-convex `Y` couples the pointer
    size positively with its neighbour's size. So a finite window of a product family exceeding
    `3.5` is not excluded by this proof.
  - Float evidence only: the relaxation with `x`, `e` at their caps and real counts
    (`finite_n_opt.py`) gives `2.00, 2.51, 2.70, 2.80, 2.88` at `n = 4, 8, 12, 16, 20`. These
    increase slowly and stay well below `3.5`, but they are local optima of a relaxation, not bounds.
- The class uses the same bulk set on both sides of the pointer and requires the leaf in `𝒜`. The
  leaf condition makes the renewal aperiodic. The general periodic case and two-sided bulk sets
  are not covered.
- Nothing about the root is decided.
