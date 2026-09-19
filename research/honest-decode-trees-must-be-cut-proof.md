---
rg: 2
id: honest-decode-trees-must-be-cut-proof
kind: route
title: Proof of the propagation theorem and the decode-tree load law for decoded unique-games reductions
target: honest-decode-trees-must-be-cut-in-ug-compositions
requires: []
artifacts:
  - experiments/ugc-propagation-load-2026-09-17/check_propagation_load.py
---

Notation is that of the target.

**Step 1 (seed lists).** Fix a site `z`. In each connected component `C_j` of
`T_z` (`j <= c_z`) fix a spanning tree `F_j` and a root `r_j`, both computed
from `T_z` in polynomial time. For a seed vector `a = (a_1, ..., a_(c_z)) in [K]^(c_z)`,
set `tau_a(r_j) = a_j` and extend along `F_j`: an edge `x_v = pi(x_u)` with `u`
labelled sets `tau_a(v) = pi(tau_a(u))`, or `tau_a(u) = pi^(-1)(tau_a(v))` if
`v` is labelled first. Each `pi` is a permutation, so this is well defined on a
tree. Put `Lambda_z = { Dec_z(tau_a|D_z) : a in [K]^(c_z) }`, a list of at most
`K^(c_z)` labels. The setting assumes `K^(c_z) <= poly(|x|)`, so the list is
computed in polynomial time.

**Step 2 (clean sites decode into their list).** If `z` is `sigma`-clean, take
`a*_j = sigma(r_j)`. Induction along `F_j` gives `tau_(a*) = sigma` on every
vertex of `C_j`, since each tree edge is satisfied by `sigma` and the unique
constraint determines one endpoint from the other. As every component meets
`D_z` and `D_z ⊆ V(T_z)`, `tau_(a*)|D_z = sigma|D_z`, so
`Dec_z(sigma|D_z) in Lambda_z`.

**Step 3 (random list choice).** Choose independently for each site a uniform
seed vector, i.e. a label `ell_z` uniform over the multiset `Lambda_z`. For a
constraint `c` counted in (YES), both sites are clean, so each decoded label
`Dec(sigma|D_(z_i))` is hit with probability `>= K^(-c_(z_i))`, independently
(the sites `z_1(c) in Z_1`, `z_2(c) in Z_2` are distinct). Then `P_c` holds with
probability `>= K^(-(c_1+c_2))`. By linearity,
`E[val_(Phi_x)(ell)] >= p K^(-(c_1+c_2)) > s`.

**Step 4 (derandomize and decide).** The expectation of `val(ell)` conditioned
on fixing the seeds of some sites is a sum over the polynomial support of `mu`
of probabilities over at most two lists, so it is computable exactly in
polynomial time. The method of conditional expectations fixes sites one by one
without decreasing it and outputs a labelling `ell*` with
`val(ell*) >= p K^(-(c_1+c_2))`. Accept iff `val(ell*) > s`. On YES inputs this
holds by Step 3. On NO inputs every labelling has value `<= s`, so we reject.
Hence `L in P`.

**Step 5 (load law).** For `i in {1,2}`,

```text
Pr_c[z_i(c) dirty] <= sum_e Pr_c[e in T_(z_i(c))] 1[sigma violates e]
                   <= kappa_i sum_e w(e) 1[sigma violates e] = kappa_i eta'.
```

A union bound over the two sides gives
`p >= p_0 - (kappa_1 + kappa_2) eta'`. Summing the first inequality with all
indicators replaced by `1` gives `E_c|T_(z_i(c))| <= kappa_i`.

**Step 6 (Corollary U).** If `(kappa_1+kappa_2) eta' < p_0 - K^(c_1+c_2) s` on
YES inputs, then `p > K^(c_1+c_2) s`, so Theorem P puts the NP-hard `L` in `P`.

**Scope.** The proof uses only that `U_x` has permutation constraints, that
`T_z` and `Dec_z` are computable, and the NO bound on `Phi_x`. It does not use
any property of the inner test, of the host spectrum, or of how `sigma` arises.
