---
rg: 2
id: finite-wreath-lift-of-internal-mf-reflection-proof
kind: route
title: Use block-monomial matrices and descend every target map coordinatewise
target: finite-wreath-lift-of-internal-mf-reflection
requires:
  - binary-leavitt-all-ranks-full-mf-radical
---

Put `m=|F|`.  The block-monomial representation sends

```text
((k_f)_(f in F),sigma)
 |->diag(k_f) P_sigma in GL_m(L_(F_2)(1,2)),             (FWLP1)
```

where `P_sigma` is the permutation matrix of the regular action of `F`.
The binary Leavitt prefix-code isomorphism identifies `GL_m(L_(F_2)(1,2))`
with `U`, proving `(FWL2)`.

Apply `pi` in every coordinate and leave the permutation actor unchanged.
This gives `(FWL3)`.  Now let `theta:K wr F->M` with `M` MF.  Its restriction
to each coordinate copy of `K` kills `ker(pi)` by `(FWL1)`.  Therefore
`theta` kills the normal product `ker(pi)^F` and descends uniquely through
`Pi`.  Conversely every map from `Q wr F` pulls back through `Pi`.  This is
the natural bijection `(FWL4)`.

Intersecting all kernels in `(FWL4)` proves `(FWL5)`.  Restrict the same
bijection to maps killing a given normal subgroup `N` and intersect kernels
again to obtain `(FWL6)`.  If `Q wr F` is MF, its radical is trivial, giving
`(FWL7)`.

If `d` normally generates `ker(pi)` in `K`, its conjugates by the coordinate
copy of `K` normally generate the kernel in that coordinate.  Conjugation by
the regular actor `F` reaches every coordinate, proving single normal
generation.  The proof used only the target-factorization property `(FWL1)`,
so it works verbatim for every other stated class.
