---
rg: 2
id: fpbs-harris-chain-majorant-is-superexponential-proof
kind: route
title: One open geodesic segment of length m-1 already gives the cluster m points, so tuple counts in one cluster grow like (mp)^m while chain sums grow at most like chi^m
target: fpbs-harris-chain-majorant-is-superexponential
requires: []
---

Complete written proof. Notation is as in the target. Only the Harris--FKG
inequality and the BK inequality for Bernoulli bond percolation are used,
together with elementary counting.

**Step 0 (the majorant).** Fix `x_0 = o`, points `x_1, ..., x_(m-1)` in `V`
and `x_m = y in N`. Each event `A_i = {x_(i-1) <-> x_i}` is increasing. By
Harris--FKG, `prod_i P_p(A_i) <= P_p(A_1 ∩ ... ∩ A_m)`. On
`A_1 ∩ ... ∩ A_m` all the points lie in `K_o`. Summing over the tuple and
using Tonelli,

```text
C_m(p) <= sum P_p(x_1,...,x_(m-1) in K_o, y in K_o ∩ N) = E_p[|K_o|^(m-1) |K_o ∩ N|] = H_m(p).
```

**Step 1 (part 1).** Since `o in N`, `|K_o ∩ N| >= 1` always. If
`theta(p) > 0`, then `|K_o|^(m-1) |K_o ∩ N| = infinity` on an event of
positive probability, because `m - 1 >= 1`. So `H_m(p) = infinity`.

**Step 2 (part 2).** `G` is infinite, connected and locally finite, so by
Konig's lemma it has a geodesic ray `o = v_0, v_1, v_2, ...`. For `n >= 0`,
the path `v_0 ... v_n` uses `n` distinct edges and visits `n+1` distinct
vertices. With probability `p^n` all its edges are open, and then
`|K_o| >= n+1`. Hence `P_p(|K_o| >= n+1) >= p^n`, and by Step 1's bound
`|K_o ∩ N| >= 1`,

```text
H_m(p) >= E_p|K_o|^(m-1) >= (n+1)^(m-1) p^n    for every n >= 0.
```

Take `n = m-1`. This gives `H_m(p) >= m^(m-1) p^(m-1) = (m p)^(m-1)`. So
`H_m(p)^(1/m) >= (m p)^((m-1)/m)`, which tends to infinity.

**Step 3 (part 3).** Let `p < p_c`, so `chi_p < infinity`. By
vertex-transitivity, `sum_(x in V) tau_p(z,x) = chi_p` for every `z`. Sum
`C_m(p)` over `y` first. Since `N ⊆ V`, this gives
`sum_(y in N) tau_p(x_(m-1),y) <= chi_p`. Then sum over `x_(m-1)`, and so on
down to `x_1`, to get `C_m(p) <= chi_p^m`. Combined with Step 2,
`H_m(p)/chi_p^m >= (m p)^(m-1)/chi_p^m = (m p/chi_p)^(m-1)/chi_p`, which
tends to infinity.

**Step 4 (part 4).** Suppose `Phi_m(K) >= #{(x_1,...,x_(m-1),y) in K^(m-1) x (K ∩ N)}`.
Then `E_(p')[Phi_m(K_o)] >= H_m(p')`, with `H_m` computed at `p'`. So
Steps 1 and 2 apply at `p'`: the bound is `infinity` if `theta(p') > 0`, and
its `m`-th root is at least `(m p')^((m-1)/m)` otherwise.

*Superposition.* Take independent Bernoulli(`p`) configurations
`omega_1, ..., omega_m` and their union `omega`. The union is
Bernoulli(`p' = 1-(1-p)^m`). If `x_(i-1) <-> x_i` in `omega_i` for each
`i`, then all the points are connected in `omega`. So
`prod_i tau_p(x_(i-1),x_i) <= P_(p')(x_0, ..., x_m in one cluster)`, which is
a majorant of the form above, with `p' >= p`.

**Step 5 (BK points the wrong way).** Let `A ∘ B` denote disjoint occurrence.
The BK inequality `P(A_1 ∘ ... ∘ A_m) <= prod_i P(A_i)` shows that the chain
product dominates the disjoint-witness chain event. So BK and Reimer give lower
bounds on `C_m`, never upper bounds.

**Step 6 (numerical check).** The script
`experiments/fpbs-fkg-chain-majorant-2026-09-17/tree_cluster_moments.py`
computes the exact cluster law on `T_3` for `p < 1/2` by Lagrange inversion.
The total masses are 1 to `10^(-9)`, and the numerical `chi_p` matches
`1 + 3p/(1-2p)`. The output shows that `(E|K|^m)^(1/m)/chi_p` grows linearly
in `m`, consistent with Step 3. The script is a check, not part of the proof.
