---
rg: 2
id: modular-three-projection-angle-proof
kind: route
title: Free-product cohomology and unitary cyclic coinvariants give the projection formula
target: modular-parabolic-restriction-is-a-three-projection-angle
requires: []
---

The characteristic-zero Mayer--Vietoris sequence for
`Gamma=<a>*<b>` and vanishing of positive-degree cohomology of the finite
factors gives

```text
H^1(Gamma,M)=M/(M^a+M^b).                                 (1)
```

Its minimum-norm representatives are precisely
`K=(M^a+M^b)^perp=ker(P_a) cap ker(P_b)`, proving `(TPA2)`.

Concretely, the class of `m` is represented by the cocycle

```text
c_m(a)=(a-1)m,                         c_m(b)=0.           (2)
```

Adding an `a`-fixed vector changes nothing, while adding a `b`-fixed vector
changes (2) by a global coboundary, so (2) realizes (1).  If `m in K`, then
`P_a m=0`; because `a` is an involution, this says `am=-m`.  Hence

```text
c_m(u)=c_m(ab)=c_m(a)+a c_m(b)=(a-1)m=-2m.               (3)
```

For a unitary operator `u`, `(u-1)M` is the orthogonal complement of `M^u`.
Thus the quotient `M/(u-1)M` is canonically and isometrically `M^u` through
`P_u`.  Applying this quotient map to (3) proves `(TPA3)`, including the
kernel and singular-value statements.
