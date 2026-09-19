---
rg: 2
id: thompson-f-iid-forest-vectors-cannot-reach-norm-one
kind: claim
title: "Every i.i.d. product test vector on pointed-forest windows of F has limiting Rayleigh quotient at most 79/80: the whole family reduces to two size laws, and a Laplace-transform obstruction caps it"
distinct_from:
  thompson-f-norm-bound-from-forest-renewal-test-vector: that certifies one member of this family (||P|| > 0.9397) and leaves open whether the family's supremum is 1; this proves the supremum is at most 79/80 < 1, for every tree-size cutoff and every choice of shape weights.
  thompson-f-moment-data-cannot-certify-nonamenability: that shows no finite list of cogrowth counts can prove ||P|| < 1, an obstruction to upper-bound certificates; this is an obstruction to a lower-bound (test-vector) family, and says nothing about ||P|| itself.
  thompson-f-32-term-cogrowth-bound-is-the-moment-optimum: that shows the moment route saturates at 0.9107; this caps the forest-product route at 0.9875 and computes its value ~0.974 (heuristic), a different family with a different invariant.
  thompson-f-iid-forest-test-vectors-are-bounded-below-one: that caps the same family at 1 - 1/1280 through a Hellinger idempotence gap H(nu, nu*nu) >= 1/8 of the bulk size law; this proves the stronger cap 79/80 through an exact reduction to J(alpha,beta)/4 (attained by split shapes) and a Laplace-transform invariant, and computes the family's value (~0.974, heuristic).
  thompson-f-norm-bound-from-iid-size-laws: that uses the size-law reduction proved here in the other direction, to certify ||P|| > 0.9698 from explicit laws; this is the ceiling.
artifacts:
  - experiments/thompson-f-iid-forest-ceiling-2026-09-19/size_law_problem.py
  - experiments/thompson-f-iid-forest-ceiling-2026-09-19/size_law_N9_640.out
  - experiments/thompson-f-iid-forest-ceiling-2026-09-19/crosscheck_w13.py
  - experiments/thompson-f-iid-forest-ceiling-2026-09-19/crosscheck_w13.out
  - experiments/thompson-f-iid-forest-ceiling-2026-09-19/ceiling_check.py
  - experiments/thompson-f-iid-forest-ceiling-2026-09-19/ceiling_check.out
  - experiments/thompson-f-iid-forest-ceiling-2026-09-19/continuum_phi.py
  - experiments/thompson-f-iid-forest-ceiling-2026-09-19/continuum_phi.out
  - experiments/thompson-f-iid-forest-ceiling-2026-09-19/spread_check.py
  - experiments/thompson-f-iid-forest-ceiling-2026-09-19/spread_check.out
  - experiments/thompson-f-iid-forest-ceiling-2026-09-19/spline_opt.py
  - experiments/thompson-f-iid-forest-ceiling-2026-09-19/spline_K24.out
---

**ESTABLISHED (analytic; the numerics are corroboration only).**

*Setting.* `S_n` is the set of pointed forests `(T_0, ..., T_{m-1}; i)` with `n` leaves in total. It
embeds in `F` so that the forest moves (pointer left/right, merge/split at the pointer) are Cayley
edges for `x_0^{±1}, x_1^{±1}` (steps 1–2 of `thompson-f-norm-bound-from-forest-renewal-test-vector-proof`).
Take any nonnegative functions `X` ("bulk") and `Y` ("pointer") on finite binary trees, both zero on
trees with more than `N` leaves, with `X ≠ 0` and `Y ≠ 0`. The **i.i.d. product vector** on `S_n` is

    f(T_0, ..., T_{m-1}; i) = Y(T_i) * prod_{j != i} X(T_j).

This is exactly the w13 ansatz family (split form, full-shape i.i.d. form and size-only form are all
special cases). Write `R_n(X, Y) = Num_n / (4 D_n)`, where `Num_n` is the sum of `f(x) f(y)` over
directed move edges and `D_n = sum f^2`.

**Theorem.**

1. *(Exact reduction.)* Let `alpha, beta` be the size laws of `X^2, Y^2` after the exponential tilt
   that makes `X^2` a probability law. For every residue class of `n` on which `D_n ≠ 0`,
   `R_n(X, Y)` has a limit as `n -> ∞`, and it is at most `J(alpha, beta')/4`, where `beta'` is `beta`
   restricted to that class and renormalised. Here

       J(alpha, beta) = 2 BC(alpha, beta)^2 + 2 sum_{j <= N} sqrt(beta_j (alpha * beta)_j),

   `BC` is the Bhattacharyya coefficient and `*` is convolution. Equality holds for the split shapes
   `w((S,U)) = sqrt(beta_s alpha_t / (beta*alpha)_{s+t}) w(S) w(U)`, `X = sqrt(alpha_|T|) w`,
   `Y = sqrt(beta_|T|) w`. So for each cutoff `N`, the supremum of the family's limiting quotient is
   `max J/4` over pairs of probability laws on `{1..N}`.
2. *(Ceiling.)* For all probability laws `alpha, beta` on `{1, 2, ...}`,
   `J(alpha, beta) <= 4 - 1/20`.

   Hence **every** i.i.d. product vector, at every cutoff `N`, has limiting Rayleigh quotient at most
   `79/80 = 0.9875`. The w13 proxy question "is `sup_N` of the ansatz optimum equal to 1?" has answer
   **no**.

**The invariant, and where every member dies.** The invariant is the Laplace transform of the two size
laws, evaluated at the `lambda` where `psi_beta(lambda) = 1/2`.
- A quotient near `4` needs both edge types near-saturated.
  - *Pointer moves* need `BC(alpha, beta) ≈ 1`: the pointer tree must look like a bulk tree.
  - *Merge moves* need `BC(alpha * beta, beta) ≈ 1`: the pointer tree must look like itself merged
    with an independent bulk tree.
- These two are incompatible, because `psi_{alpha*beta} = psi_alpha psi_beta`. At `psi_beta = 1/2`,
  any `alpha` close to `beta` has `psi_{alpha*beta} ≈ 1/4`, far from `1/2`.
- Quantitatively, `TV(alpha,beta) + 2 TV(alpha*beta, beta) >= 1/2`.
- Every member dies at the **merge step**: an independent sum of sizes cannot be self-similar in law.

**Value of the family (numerics, not part of the theorem).**
- *Exact optimum.* The optimum of `J/4` over laws on `{1..N}`, by L-BFGS with exact gradient
  (`size_law_problem.py`), is `0.87771, 0.91179, 0.92897, 0.94002, 0.94750, 0.95279, 0.95665` at
  `N = 9, 20, 40, 80, 160, 320, 640`.
  - The first four equal the w13 split-ansatz optima to all printed digits.
  - `crosscheck_w13.py` feeds the split construction through w13's self-tested `certify_window.py`.
    It reproduces `J` exactly as `2H(1)/Q(1)`, and the finite windows approach `J` like `1/n`.
- *Log-scale spline family* (`spline_opt.py`, 24 knots per law):
  - `0.964941` at `N = 10^4`, `0.968087` at `10^5`, `0.969877` at `10^6`;
  - the optimal size densities are a bump in `ln k`.
- *Continuum limit (heuristic).* Laws spread over `ln k` give
  `J -> Phi[A] = 2 (∫ sqrt A')^2 + 2 ∫ sqrt((uA)')`, where `A` is the cdf of `alpha` in the quantile
  coordinate `u` of `beta`.
  - The maximum is `sup Phi/4 ≈ 0.97436` (`continuum_phi.py`). `A = u^0.87` already gives `0.97410`.
  - Explicit laws converge to it slowly, roughly like `(ln N)^{-1.5}` (`spread_check.py`).
  - Conjecture: the family's supremum over all `N` is about `0.9744`. The theorem proves `<= 0.9875`.

**What survives.** Test vectors whose neighbouring trees have **correlated** sizes, such as a Markov
chain of tree sizes along the forest or a pointer tree coupled to its right neighbour, escape the
obstruction. There the merge constraint no longer forces `alpha * beta ≈ beta` for independent laws.
Følner-type sets of forests, if they exist, must use such correlations. A proxy for amenability
must therefore leave the i.i.d. product class.

Proof route: `thompson-f-iid-forest-vectors-cannot-reach-norm-one-proof`.

## Attempts

- **Sharpening the constant.** The proof loses in two places: `TV <= sqrt 2 H` and a single Laplace
  point. The numerics say the truth is about `0.9744`, against the proved `0.9875`. A two-point or
  full-transform version of the Laplace step should close part of the gap. OPEN, low priority: it does
  not change the conclusion.
- **Finite windows with `n`-dependent weights.** The theorem is about the `n -> ∞` limit at fixed
  `(X, Y)`. That is the quantity the ansatz optimises and the limit of every fixed certificate. A
  vector optimised for one finite window `n` is not covered. OPEN.
