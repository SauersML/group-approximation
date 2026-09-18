---
rg: 2
id: fpbs-spine-increment-activation-gate-proof
kind: route
title: Run the Bihari argument of the operator gate with right-endpoint kernels and an atomless measure over the spine-augmented exhaustion, feed it the split bounds (R) and (A), and contradict collapse
target: fpbs-spine-increment-activation-gate
requires:
  - fpbs-annealed-pivotal-factorization-off-spine-bridges
  - fpbs-quenched-bk-russo-collapse-operator-gate
  - fpbs-continuous-activation-collapse-family
---

Notation as in the target. Norms are `l2 -> l2`. For nonnegative matrices,
`0 <= A <= B` entrywise implies `||A|| <= ||B||`
(`fpbs-quenched-bk-russo-collapse-operator-gate-proof`, Step 6.1).

## 1. Theorem 1

Put `g(t) = ||X_t||`. Then `g >= 1` (unit diagonal), `g` is nondecreasing,
and `g` is finite, since `W` is finite. Fix `s < t` and `eta in (0,1)`.

The function `c(x) = kappa((t_0,x])` is continuous, because `kappa` is finite
and atomless. So there is a partition `s = x_0 < ... < x_N = t` with
`kappa_i := kappa((x_i, x_{i+1}]) < eta` for every `i`.

Write `g_i = g(x_i)`. From `0 <= X_{x_{i+1}} - X_{x_i} <= kappa_i X_{x_{i+1}} J_W X_{x_{i+1}}`,
monotonicity of the norm and `||J_W|| <= d`,

```text
g_{i+1} <= g_i + ||X_{x_{i+1}} - X_{x_i}|| <= g_i + d kappa_i g_{i+1}^2 .
```

Dividing by `g_i g_{i+1}`, and using `g_i >= 1`:

```text
1/g_i - 1/g_{i+1} <= d kappa_i g_{i+1}/g_i = d kappa_i + d kappa_i (g_{i+1} - g_i)/g_i
                  <= d kappa_i + d eta (g_{i+1} - g_i).
```

Summing over `i` gives `1/g(s) - 1/g(t) <= d kappa((s,t]) + d eta g(t)`. Let
`eta -> 0`.

**Exhaustion.** With `s = t_0`, `g_j(t_0) <= ||T_{t_0}||`, so
`g_j(t) <= K(t) := ||T_{t_0}|| / (1 - d ||T_{t_0}|| kappa((t_0,t]))` uniformly in
`j`. Extend `X^{(j)}_t` by the identity off `W_j`. For finitely supported
`f,h >= 0`, the supports eventually lie in `W_j`, and monotone convergence
gives `<f, T_t h> = lim_j <f, X^{(j)}_t h> <= K(t) |f| |h|`. So
`||T_t|| <= K(t)`. ∎

## 2. Theorem 2

Take the spine-augmented kernels `X^{(j)}_t = X^{Lambda_j}_t` on `W_j = V(Lambda_j)`.

* **Hypotheses of Theorem 1.** They are nonnegative with unit diagonal. They
  are nondecreasing in `t`, because `omega_t ∩ (Lambda ∪ Z_t)` increases in
  `t`.
* **Starting point.** `Z_{t_0} = ∅` gives `X^{Lambda}_{t_0} = T^{Lambda}_{t_0} <= T_{t_0}`
  entrywise.
* **Convergence.** `omega_t ∩ (Lambda_j ∪ Z_t)` increases to `omega_t`. An open
  path is finite, so `X^{Lambda_j}_t(u,v)` increases to `T_t(u,v)`.

By Theorem 2 of `fpbs-annealed-pivotal-factorization-off-spine-bridges`,
`X_t - X_s = D^R_{s,t} + D^A_{s,t}`, with `D^R_{s,t} <= 2(t-s) X_t J_W X_t` and
`D^A_{s,t} <= beta_s (S_t - S_s) beta_s`. Under (AG*) the second bound gives
(AG), `D^A_{s,t} <= kappa_A((s,t]) X_t J_W X_t`. Hence

```text
X_t - X_s <= kappa((s,t]) X_t J_W X_t,        kappa = 2 Leb + kappa_A,
```

and `kappa` is finite and atomless on `[t_0, t_0+delta]`. Theorem 1 gives the
bound on `||T_t||`.

If `inf_{u,v} T_t(u,v) = c > 0`, then for finite `F ⊆ V`,
`<1_F, T_t 1_F> >= c |F|^2`, so `||T_t|| >= c |F|`. On an infinite graph that
is unbounded, a contradiction. ∎

## 3. Corollary 3

Suppose (AG) held for some `delta`, exhaustion and `kappa_A`. The measure
`kappa = 2 Leb + kappa_A` is atomless, so `kappa((t_0,t]) -> 0` as `t ↓ t_0`.
Choose `t in (t_0, min(t_0 + delta, t_0 + eps))` with
`d ||T_{t_0}|| kappa((t_0,t]) < 1`. Theorem 2 gives `||T_t|| < infinity`,
which contradicts `inf T_t > 0`. So (AG) fails. Since (AG*) implies (AG),
(AG*) fails too.

**Hypotheses for the continuous-activation family.** By
`fpbs-continuous-activation-collapse-family`, (C1) and the construction
(Step 5 of its proof):

* `Z_t = {e : tau_e <= t}` is `M`-measurable, with `M` independent of `U`;
* it is nondecreasing and connected;
* `tau_e > p_c`, so `Z_{p_c} = ∅`;
* (C0) gives `T_t >= theta_xi(t)^2 > 0` for `t > p_c`.

On a critical-L2 spine graph, `||T_{p_c}|| < infinity`, as in Corollary 3 of
`fpbs-quenched-bk-russo-collapse-operator-gate`. ∎
