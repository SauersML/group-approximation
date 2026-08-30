---
rg: 2
id: stw77-quotient-descent-proof
kind: route
title: Push nuclear approximations, Cuntz inequalities, and central isometries through a quotient
target: stw77-hypotheses-and-stability-descend-to-quotients
requires: []
---

## Proof

Composition with `q` carries every finite-color nuclear approximation for
`phi` to one for `q phi`, so nuclear dimension cannot increase.

Every positive element `c` of `(q phi)(A)` has a positive lift `a in A_+`
under the surjection `A->(q phi)(A)`.  If `c` is nonzero, then `phi(a)` is
nonzero and hence properly infinite.  The Cuntz inequality

```text
2[phi(a)] <= [phi(a)]
```

passes through the quotient, giving `2[c]<=[c]`; thus `c` is properly
infinite.

Finally, two central orthogonal isometries representing O-infinity-stability
map coordinatewise to central orthogonal isometries for `q phi`.  Equivalently,
the induced unital homomorphism on relative sequence algebras carries a
unital copy of `O_infinity` to a nonzero, hence injective, unital copy in the
quotient relative commutant.
