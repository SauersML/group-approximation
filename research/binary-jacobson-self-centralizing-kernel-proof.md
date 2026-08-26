---
rg: 2
id: binary-jacobson-self-centralizing-kernel-proof
kind: route
title: Centralize the finitary transvections and use simplicity of the kernel
target: binary-jacobson-head-retaining-homomorphisms-are-faithful
requires:
  - binary-jacobson-elementary-mark-is-finite-quotient-invisible
---

Write `Omega=N x {1,...,5}` and let `V=directSum_Omega F_2`.  The standard
shift/backshift realization of `J` is faithful, hence so is the induced
action `E<=GL(V)`.  The subgroup `L` contains every finitary transvection

```text
tau_(u,v): e_v |-> e_v+e_u               (u!=v).       (1)
```

Suppose `g in GL(V)` centralizes `L`.  Commuting with all `(1)` forces `g`
to preserve every coordinate line and forces the scalar on any two lines to
be equal: apply the equality `g tau_(u,v)=tau_(u,v) g` to `e_v`, and then
vary `u,v`.  Thus `g=lambda I`.  Over `F_2` the only invertible scalar is
`lambda=1`.  Intersecting this centralizer with `E` proves `(JHF2)`.

Now let `phi:E->G` retain `w`.  Since `w in L\{1}` and `L` is simple,
`ker(phi) intersect L` is not `L` and therefore is trivial.  For any
`k in ker(phi)`, normality of `L` gives

```text
[k,L] <= ker(phi) intersect L = 1.                    (2)
```

Hence `k in C_E(L)=1`.  This proves `(JHF3)` and the claim.
