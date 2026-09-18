---
rg: 2
id: view-local-branch-selectors-gauge-blindness-proof
kind: route
title: The branch functional lies outside the view span plus the B-subspace, so a uniform gauge makes the branch bit independent of everything a parity-faithful selector reads, and McDiarmid plus a union bound handles witness menus
target: view-local-branch-selectors-are-gauge-blind
requires: []
artifacts:
  - experiments/ugc-heretic-2026-09-17/check_gauge_blind_selectors.py
---

Notation is as in the target claim. The proof is self-contained.

**Step 0 (gauge is value-preserving).**
`<m_j, A + z> + (b_j + <m_j, z>) = <m_j, A> + b_j`. So `A` satisfies equation `j`
of `I` iff `A + z` satisfies equation `j` of `I^z`. In particular, whether `U_e`
is satisfied by `t + z` in `I^z` does not depend on `z`, and the vertices,
subspaces and weights of `D(I^z)` equal those of `D(I)`.

**Step 1 (linear algebra).** Assume (F) at `e`: `Q_e meet X_U = H_U`. Suppose
`x_e in L' + Q_e`, say `x_e = y + q`. Then `q = x_e + y` lies in `X_U`, since
`x_e, y in L <= X_U`. So `q in Q_e meet X_U = H_U`, and `x_e + y in L meet H_U = {0}`.
Hence `x_e = y in L'`, which contradicts `x_e in L \ L'`.

**Step 2 (independence).** The map
`phi(z) = ((<m_j,z>)_(j in J_e), (<y_i,z>)_(i), <x_e,z>)` is linear, where the
`y_i` form a basis of `L'`. Its last coordinate is not a linear combination of the
others, because `x_e notin Span(m_j : j in J_e) + L'` (Step 1). So the image of a
uniform `z` is uniform on a product of the image of the first two blocks with
`F_2`. That is, `<x_e, z>` is a uniform bit independent of the view and of `z|L'`.

The selector's output at `e` is a function of `M`, `b|J_e` and the B-label, and
these are affine in the first two blocks. The target bit `(t+z)(x_e) = t(x_e) + <x_e,z>`
is the uniform bit shifted by a constant. So the agreement probability is exactly
`1/2`.

**Step 3 (expectation).** Sum over edges. An (F)-edge contributes
`w_e * 1[U_e sat by t] / 2`. Any other edge contributes at most `w_e`. So
`E_z f_t <= 1/2 + w_bad/2`.

**Step 4 (concentration).** The indicator for edge `e` is a function of `z`
restricted to `S_e`, because the view uses the supports of the `m_j` with
`j in J_e`, and the B-label and branch bit use window coordinates. McDiarmid's
bounded-differences inequality with `c_i = d_i` gives
`Pr[f_t - E f_t >= gamma] <= exp(-2 gamma^2 / sum d_i^2)`. Moreover
`sum_i d_i = sum_e w_e |S_e| <= s`, so `sum_i d_i^2 <= d_max s`.

**Step 5 (menus).** Equivariance gives
`max_(t' in T(I^z)) hon_(t')(S(I^z)) = max_(t in T(I)) f_t(z)`. A union bound
over `T(I)` finishes the proof. For clustered menus, flipping `t_i` changes `f_t`
by at most `d_i`, so `f_t` is `d_max`-Lipschitz in Hamming distance, and a
`rho n`-net costs an additive `rho n d_max`. QED.

The artifact confirms Steps 1 and 2 exhaustively on 480 windows. For every window
it enumerates all gauges and all selectors at once, through per-cell counts.
