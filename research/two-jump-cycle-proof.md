---
rg: 2
id: two-jump-cycle-proof
kind: route
title: Put opposite phases on the two halves of a cyclic orbit
target: two-jump-cycle-refutes-functional-calculus-gauge-bound
requires: []
---

The quotient of two consecutive values of `c_L` is `-1` only when the
cycle crosses from the first half to the second or crosses back at the
periodic boundary.  This proves `(TJC2)`.

If `d` is another solution, then

```text
d psi(d)^(-1)=c_L psi(c_L)^(-1),
```

so `c_L^*d=psi(c_L^*d)`.  The fixed algebra of the transitive cyclic shift
on `C^(Z/LZ)` consists of the constants.  Hence `d=zeta c_L` for a scalar
unitary `zeta`.  Half of its values are `zeta` and half are `-zeta`, and

```text
|zeta-1|^2+|-zeta-1|^2
 = (2-2 Re(zeta))+(2+2 Re(zeta))=4.
```

After the half-half average this is `(TJC3)`.  The calculation is exact for
every even `L`.

