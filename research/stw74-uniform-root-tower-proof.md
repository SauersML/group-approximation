---
rg: 2
id: stw74-uniform-root-tower-proof
kind: route
title: Use compactness of the unit to freeze the root multiplicity along spectral cutdowns
target: stw74-counterexample-has-uniform-root-towers
requires:
  - stw74-counterexamples-are-unstably-projectionless
  - stw74-every-nonzero-cu-class-is-a-finite-unit-root
---

Fix `0!=a in D_+`, rescaled to norm at most one.  Choose a strictly decreasing
sequence `epsilon_k` tending to zero such that every
`(a-epsilon_k)_+` is nonzero, and set

```text
y_k=[(a-epsilon_k)_+].
```

Functional calculus gives `y_k<<y_(k+1)` and `sup_k y_k=[a]`.

Choose `n` with `n[a]=[1_A]=u`.  Addition preserves increasing suprema, so

```text
u = n[a] = sup_k n y_k.
```

Since `u` is compact, `u<=n y_k` for some `k`.  The unit is the largest
element and properly infinite, so `n y_j<=n u=u` for every `j`.  Hence
`n y_j=u` for all `j>=k`.  Discard the finite initial segment and relabel to
obtain the asserted sequence `(x_k)` with one fixed multiplicity `n`.

If a nonzero projection class `[p]` were below some `x_k`, then `p` would be
Cuntz below `(a-epsilon_k)_+`.  A projection Cuntz below a positive element is
Murray--von Neumann equivalent to a projection in its hereditary subalgebra.
This would give a nonzero projection in

```text
Her_A((a-epsilon_k)_+) subset D,
```

contrary to projectionlessness of `D`.  Thus every `x_k` is projective-free.
