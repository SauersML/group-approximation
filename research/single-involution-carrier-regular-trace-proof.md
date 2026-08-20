---
rg: 2
id: single-involution-carrier-regular-trace-proof
kind: route
title: Read the identity coefficient and then diagonalize the selector subgroup
target: single-involution-cannot-be-a-nonlinear-selector-carrier
requires: []
---

The coefficient of the identity in `e_chi` is `1/|A|`.  If a term of
`d e_chi` were the identity, then `da=1` for some `a in A`, whence
`d=a^(-1) in A`, contrary to the first case.  This proves the first two
equalities in `(SIC2)`.  Since `p` and `e_chi` are projections,

```text
||p e_chi||_2^2=tau(e_chi p e_chi)=tau(p e_chi),
```

which proves the last equality without assuming that `d` normalizes `A`.

If `d in A`, the minimal projections `(e_chi)` simultaneously diagonalize
`C[A]`, and `d e_chi=chi(d)e_chi`.  Substitution in `p=(1-d)/2` proves
`(SIC3)`.  Evaluation `chi |-> chi(d)` is a nonzero linear functional on the
binary character space when `d!=1`, so either sign fiber is affine.
