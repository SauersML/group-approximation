---
rg: 2
id: hs-gap-failure-cheap-refinement-proof
kind: route
title: Apply weighted median coarea inside the block and use the exact refinement identity
target: hs-gap-failure-cheap-refinement
requires:
  - weighted-median-coarea-relative-cut
  - block-refinement-boundary-increment
---

Failure of the scalar gap supplies a self-adjoint `x in pM_dp` with
`tau_p(x)=0`, `||x||_(2,p)=1`, and

```text
E=sum_s ||a_sx-xa_s||_(2,p)^2 < kappa^2.
```

Every `a_s=pU_sp` is a contraction.  Apply
`weighted-median-coarea-relative-cut` in the normalized corner.  It gives a
nonzero `q<=p` with `tau_p(q)<=1/2` and

```text
sum_s ||[a_s,q]||_(2,p)^2
 < 2 sqrt(2m) kappa tau_p(q).
```

Convert corner norms to ambient normalized Hilbert--Schmidt norm by
multiplying squared norms and traces by `tau(p)`:

```text
sum_s ||[pU_sp,q]||_2^2
 < 2 sqrt(2m) kappa tau(q).
```

For each generator, `block-refinement-boundary-increment` says that replacing
`p` by `q` and `r=p-q` adds exactly twice this internal squared-commutator
energy.  Summing over `s` therefore gives an increase strictly below

```text
4 sqrt(2m) kappa tau(q),
```

which is `(CHEAP)`.
