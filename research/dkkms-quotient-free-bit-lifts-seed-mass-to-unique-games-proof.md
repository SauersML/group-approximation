---
rg: 2
id: dkkms-quotient-free-bit-lifts-seed-mass-to-unique-games-proof
kind: route
title: Put the branch bit on a canonical vector of the quotient L + H_U so the honest class label can be corrected by one functional, count seed lifts per smoothing to get the product posterior, and run Hoeffding on the per-block log ratios of the generating hyperplane against each competitor
target: dkkms-quotient-free-bit-lifts-seed-mass-to-unique-games
requires:
  - dkkms-2to1-instances-satisfy-selector-decoding-hypotheses
  - dkkms-seed-law-is-uniform-in-regime-and-far-in-window
artifacts:
  - experiments/ugc-free-bit-2026-09-17/quotient_seed_posterior.py
---

The notation is that of the target. Here `pi : X_U -> Y` is the quotient map.
`[N, j]` is the number of `j`-subspaces of an `N`-space.

## Premises used

- **(I)** The DKKMS instance, as quoted verbatim (TR16-198 §4.2) in
  `dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`. That includes
  the per-tuple edge process (`V`, then `L'` uniform in `Gr(X_V, l-1)`, then
  `L = L' + <x>` with `x` uniform and `L meet H_U = 0`), folding by
  `L + H_U`, unfolding by `h_U`, and the 2-to-1 constraint
  `sigma restricted to L' = sigma'`.
- **(U)** Theorem U of `dkkms-seed-law-is-uniform-in-regime-and-far-in-window`.
  It is used only for the flat side of Corollary D.

## Proof of Theorem F

*(1) Bijectivity.* `L' meet H_U <= L meet H_U = 0`. So `P := L' + H_U` is a
hyperplane of `S_C`, and `y_e` lies outside it, which gives
`S_C = L' ⊕ H_U ⊕ <y_e>`. A label `sigma_C` fixes `tilde sigma_U`, and hence
the pair `(sigma', b)`. Conversely, `(sigma', b)` together with `h_U` fixes
`tilde sigma_U` on all of `S_C`, and hence `sigma_C`. So every constraint is a
bijection between two alphabets of size `2^l`.

Computing `S_C`, `P` and `can(S_C, P)` is linear algebra over `F_2` in
dimension `3k`.

*(2) Soundness.* Forgetting `b` sends a lift labelling to a labelling of `G`.
The A-label becomes `tilde sigma_U restricted to L`, and the B-label becomes
`sigma'`. Every lift constraint it satisfies still holds without the bit.

*(3) Completeness.* Let `U` be a member of `C` whose equations `a` satisfies.

- Then `a` restricted to `H_U` is `h_U`, and `phi_C` vanishes on `H_U`, which
  lies inside `Q_C`. So `a + t phi_C` with `t = a(y_C)` agrees with `h_U` on
  `H_U`.
- It also agrees with `sigma_C` on `R_C`, so it is the unfolding
  `tilde sigma_U`. This holds for every such `U` in the class simultaneously.
  This is the step Proposition 4 needed folding-compatibility for: in the
  quotient, the class label and its unfolding are one functional on `S_C`.

Now take an edge `e` of this `U` with `L' + H_U = Q_C`.

- On `Q_C` we have `phi_C = 0`, so `tilde sigma_U` restricted to `L'` equals
  `a` restricted to `L'`, which is the B-label.
- `y_e = can(S_C, Q_C) = y_C`, so
  `tilde sigma_U(y_e) = a(y_C) + a(y_C) phi_C(y_C) = 0 = b`.

So within class `C` the satisfied mass is at least
`w(Q_C | C) - Pr[U unsatisfied by a | C]`. Averaging over `C` by edge mass
gives `>= E_C max_Q w(Q|C) - eps_out = 1 - xi - eps_out`.

The B-label `(a restricted to L', 0)` does not depend on the edge, so the
labelling is well defined.

## Proof of Lemma P

**Step 1: the class law.** Fix the variable blocks of `U`. The right-hand
sides do not enter the edge process, so `w(. | C)` depends only on `Lbar`.

Given `L'` with `L' meet H_U = 0`, its image `Q = pi(L')` has dimension
`l - 1`. The class `Lbar = Q + <xbar>` has `xbar = pi(x)` uniform in `Y`, and
validity is exactly `xbar` not in `Q`. So

`Pr[Lbar | pi(L') = Q] = 2^(l-1) / (2^(2k) - 2^(l-1))`

for each of the `l`-spaces `Lbar` containing `Q`, which does not depend on
`Q`. Hence `w(Q | C)` is proportional to `Pr[pi(L') = Q]`.

**Step 2: the law of `pi(L')` given `V`.** Suppose `V` smooths `s` blocks,
keeping variable `v_i` in smoothed block `i`. Then `W_V := pi(X_V)` is

`⊕_kept Y_i ⊕ ⊕_smoothed <ebar_(v_i)>`,

and `ker(pi restricted to X_V)` is the span of the `k - s` kept all-ones
vectors.

- The `(l-1)`-spaces `R <= X_V` with `pi(R) = Q` exist iff `Q <= W_V`, that is,
  iff `f_(i,v_i)` vanishes on the block-`i` image of `Q` for every smoothed
  `i`.
- When they exist they are the graphs of the linear maps from `Q` to that
  kernel. There are `2^((l-1)(k-s))` of them.

With `N = 3k - 2s`, we have
`[N, l-1] = 2^((l-1)(N-l+1)) gamma_N` and
`gamma_N / gamma_inf in [1, 1 + 2^(l+1-N)]`. So

`Pr[pi(L') = Q | V] = c_k 2^((l-1)s) (gamma_inf/gamma_N) 1{Q <= W_V}`,

where `c_k` depends only on `(k, l)`.

**Step 3: the product.** Averaging over the independent block choices of `V`,
where a block is kept with probability `1 - beta` and smoothed onto
variable `v` with probability `beta/3`, gives

`Pr[pi(L') = Q]  ∝  prod_i ((1 - beta) + (beta/3) 2^(l-1) n_i(Q))`,

up to the factor `gamma_inf/gamma_N`, which lies in `[(1 + 2^(l+1-k))^(-1), 1]`
since `N >= k`.

The artifact checks this exactly by enumeration at `l = 2` and `k = 2, 3`.

- The class-averaged `L^1` error is at most `1.2 * 10^(-2)` at `k = 2`.
- At `k = 3` it is at most `4.6 * 10^(-3)`.

## Proof of Theorem H

**The product law.** Given `V`, Step 2 shows that `pi(L')` is uniform on
`Gr(W_V, l-1)`, and `xbar` is uniform on `Y \ pi(L')`. Here
`dim W_V = 2k - s >= k`.

The product law replaces these with `l - 1` i.i.d. uniform generators
`rbar_j` of `W_V` and an independent uniform `xbar` in `Y`. The two laws
differ in total variation by at most `2^(l-k)`, which covers the events that
the generators are dependent or that `xbar` lies in their span. Under the
product law the blocks are independent.

**The rows.** Write each hyperplane `Q` of `Lbar` as `ker psi`, with `psi` a
nonzero functional in the coordinates `(rbar_1, ..., rbar_(l-1), xbar)`.

- The generating seed is `psi_0 = (0, ..., 0, 1)`.
- For each block `i` and each `v`, let `m_(i,v) in F_2^l` be the vector of
  values of `f_(i,v)` on the generators. Then
  `n_i(ker psi) = #{v : m_(i,v) in {0, psi}}`.
- Also `m_(i,1) + m_(i,2) + m_(i,3) = 0`.

**The log ratio.** Fix `psi != psi_0` and put
`Z_i := ln F(n_i(psi_0)) - ln F(n_i(psi))`. Then `|Z_i| <= Lambda`. The cases
are as follows.

- **Kept block.** Here `(m_(i,1), m_(i,2))` are i.i.d. uniform on `F_2^l`. The
  law is `GL_l`-invariant, and some `g` in `GL_l` swaps `psi_0` and `psi`. So
  `Z_i` is symmetric and has mean `0`.
- **Smoothed block, variable `v`.** Here `rbar_j = c_j ebar_v` with `c` uniform
  in `F_2^(l-1)`. We have `f_(i,u)(ebar_v) = 1` for `u != v`, so
  `m_(i,v) = f_(i,v)(xbar) psi_0` and `m_(i,u) = (c, f_(i,u)(xbar))` for `u != v`.
  - **(A)** `f_(i,v)(xbar) = 1`, probability `1/2`. Then `m_(i,v) = psi_0`, so
    `n_i(psi_0) >= 1`. The two other rows differ by `psi_0`, so at most one of
    them lies in `{0, psi}`, giving `n_i(psi) <= 1`. Hence `Z_i >= 0`.
    Moreover `n_i(psi) = 0`, and so `Z_i >= lambda`, unless `c = 0` or `c` is
    the first `l - 1` coordinates of `psi`. Those have total probability at
    most `2^(2-l)`.
  - **(B)** `f_(i,v)(xbar) = 0`. Then `m_(i,v) = 0` and both other rows equal
    `(c, b)`, which is uniform in `F_2^l`. Here `n_i(.) = 1 + 2 * 1{(c,b) in {0, .}}`
    is exchangeable in `(psi_0, psi)`, so `E Z_i = 0`.

So `E Z_i >= beta * (1/2) * (1 - 2^(2-l)) * lambda = mu`.

**The bound.** By Hoeffding,
`Pr[sum_i Z_i < k mu/2] <= exp(-k mu^2 / (8 Lambda^2))`. Take a union over the
`2^l - 2` competitors. Off that event, Lemma P gives
`w(psi)/w(psi_0) <= 2 e^(-k mu/2)` for every `psi`, so
`1 - w(psi_0 | C) <= 2^(l+1) e^(-k mu/2)`.

Finally, `max_Q w(Q|C)` is at least `sum_Q w(Q|C)^2`, and
`E_C sum_Q w(Q|C)^2 = E_edge w(pi(L') | C)`. So `xi <= E_edge [1 - w(psi_0 | C)]`.
Adding the total-variation terms (`2^(l-k)` for the product law, and
`2^(l-k)` for the reweighting of `V` by validity) gives the stated bound.

The artifact's Monte Carlo under the product law, over 200 samples, measured
`E w(Q_0|C)` as follows.

| `l` | `beta` | `k = 50` | `k >= 200` |
|---|---|---|---|
| 3 | 0.5 | 0.83 | 1.0000 |
| 4 | 0.5 | 0.94 | 1.0000 |

At `beta = ln ln k / k` it stays within `0.002` of `1/(2^l - 1)` from `k = 200`
on.

## Proof of Corollary D

**Flat side.** We have `w(Q|C) = E_(L|C) w(L meet Q | L)`, since the
hyperplanes of `L` correspond bijectively to those of `Lbar`. So

`E_C max_Q w(Q|C) <= E_L max_R w(R|L) <= 1/(2^l - 1) + 6 d`

by (U), since (R) implies the hypotheses of Theorem U.

**Decomposition.** See `ugc-from-dkkms-soundness-at-heavy-smoothing`.

## Remark (not used)

At fixed `beta` the free bit is a polynomial-time, parity-leaking selector
with near-perfect YES lifts. This leads to the following observation, which
is not checked here. If the rigidity-plus-decoding argument of
`near-perfect-selectors-on-rigid-dkkms-instances-put-np-in-rp` extended to
such points, it would put `NP` in `RP`. So a soundness proof at heavy
smoothing, if it exists, should not be expected to pass through Theorem R's
outer-honesty conclusion.
