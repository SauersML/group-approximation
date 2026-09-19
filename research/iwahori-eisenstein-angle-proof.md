---
rg: 2
id: iwahori-eisenstein-angle-proof
kind: route
title: Retain the opposite cusp-width vectors and estimate the residue mismatch
target: iwahori-eisenstein-angle
requires: []
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
---

Write `C=PSL_2(Z)` and let `B` be its index-three Iwahori subgroup.  Its two
cusp stabilizers are generated, in opposite-unipotent coordinates, by

```text
u^2, v                    inside the first vertex,
u',  w^2                  inside the second vertex,
```

where the edge identifications are `u^2=u'` and `v=w^2`.  Thus the local
degrees of the two cusp maps are respectively

```text
(2,1)                    and                    (1,2). (EIP1)
```

For an odd principal congruence kernel `N`, reduction modulo two is
surjective.  The parabolic generator at every cusp has odd width and hence
acts as a transposition on the three sheets of `N cap B <= N`.  Its sheet
orbits have sizes one and two.  Therefore every cusp of `N` has exactly two
Iwahori lifts, of ramification indices one and two, and the two lift families
are each in bijection with the cusp set of `N`.  Formula `(EIP1)` shows that
the opposite embedding reverses the two indices.

In the residue description of Eisenstein cohomology, pullback across a cusp
of local degree `e` multiplies its residue by `e`.  Cusp bijections and the
coefficient action are unitary in the cusp-count norm.  Hence there are
unitaries `A,B,C,D` for which the two pullbacks are

```text
res_1 f=(2Af,Bf),                 res_2 g=(Cg,2Dg).    (EIP2)
```

Put `a=||f||`, `b=||g||`.  Expanding `(EIP2)` gives

```text
||res_1 f-res_2 g||^2
 =5a^2+5b^2-4 Re<Af,Cg>-4 Re<Bf,Dg>
 >=5(a^2+b^2)-8ab
 =a^2+b^2+4(a-b)^2.                                  (EIP3)
```

This proves `(EIA1)`.  Since
`sqrt(a^2+b^2)>=(a+b)/sqrt(2)`, it also proves `(EIA2)`.

For a congruence coefficient representation, pass to a principal odd-level
kernel on which the coefficient action is trivial.  The residue space is
then the scalar cusp space tensored with the coefficient Hilbert space; the
four additional coefficient transports in `(EIP2)` remain unitary, so the
same estimate applies verbatim.  The residue-sum-zero subspace is preserved
by both pullbacks, and restriction of a bounded-below operator to that
subspace cannot decrease the displayed lower bound.  This completes the
uniform Eisenstein calculation.
