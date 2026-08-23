---
rg: 2
id: literal-involution-agreement-mass-proof
kind: route
title: Identify the agreement space with the fixed space of one cyclic translation
target: distinct-literal-involutions-agree-on-at-most-half-the-canonical-mass
requires:
  - finite-support-one-sided-stabilizers-are-torsion
---

Multiplying `(LIM1)` on the left by `b` gives `(g-1)q=0`.  The finite-support
stabilizer theorem already forces `g` to have finite order whenever `q` is
nonzero.  If its order is `n`, the fixed-space projection for left
translation by `g` in the canonical group von Neumann algebra is

```text
e_g=(1/n)sum_(k=0)^(n-1)g^k.                           (LIM4)
```

Every vector in the range of `q` is fixed by `g`, hence `q<=e_g`.  The
identity coefficient of `e_g` is `1/n`, so canonical trace monotonicity gives
`tau(q)<=1/n`.  The infinite-order case has no nonzero finite-support fixed
projection, also directly by the cited stabilizer theorem.
