---
rg: 2
id: hs-one-level-from-selection-load
kind: route
title: Sum the scale-sensitive refinement charges over the selection tree
target: hs-one-level-expander-block-decomposition
requires:
  - hs-refinement-selection-load-vanishes
  - hs-witness-cheap-refinement
---

Let `kappa_0` and `omega(delta)` be supplied by
`hs-refinement-selection-load-vanishes`, and take the leaf projections
`p_1,...,p_k` of its finite binary tree.  They are orthogonal and sum to `1`,
so there is no discarded trace.  By the leaf condition, every block has the
required scalar adjoint gap with the dimension-independent constant
`kappa_0`.

Initially the one-block partition `{1}` has zero generator-boundary energy.
At an internal node `p`, apply `hs-witness-cheap-refinement` to its chosen
witness.  Splitting `p` into `q_p,p-q_p` increases the boundary energy summed
over all generators by at most

```text
4 sqrt(2m) tau(q_p) sqrt(E_p).
```

The exact refinement identity means these increments telescope from the root
partition to the leaf partition; no previously paid outside-boundary term is
counted again.  Therefore

```text
sum_(s in S) sum_i ||[phi(s),p_i]||_2^2
 <= 4 sqrt(2m) sum_(p internal) tau(q_p) sqrt(E_p)
 <= 4 sqrt(2m) omega(delta) -> 0.
```

In particular the same bound holds for each fixed generator separately.
Taking

```text
eps(delta)=4 sqrt(2m) omega(delta)
```

(and enlarging it harmlessly if the house formulation also wants a positive
trace-discard allowance) proves the one-level normalized-HS Kun decomposition.
