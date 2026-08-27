---
rg: 2
id: unsquared-defect-mf-invisible-proof
kind: route
title: Pull the quotient collapse back through the marked sign
target: unsquared-defect-mf-invisible
requires: [literal-mark-quotient-not-mf]
---

## Why sufficient

The route to `literal-mark-quotient-not-mf` shows more than non-MF-ness:
it places the image `ubar` of `u` in `Rad_MF(E/<w>)`, as the collapse
commutator `[v_1, dbar]^{-1}` of the level-one block witness.  Since
`w in Rad_MF(E)` (the manuscript's Theorem A, formalized), the radical
pullback `cor:pullback`
(`TorsionCompressionCollapse.actualCoronaMFResidual_eq_comap_quotient`,
formalized) gives

```text
Rad_MF(E) = q^{-1}(Rad_MF(E/<w>)),   q : E -> E/<w>.
```

`q(u) = ubar` lies in `Rad_MF(E/<w>)`, so `u in Rad_MF(E)`.
