---
rg: 2
id: finite-affine-sl3-root-shell-overlap-proof
kind: route
title: Use the natural affine action of SL3(F2) and its finite Bernoulli lamp group
target: finite-affine-sl3-root-shell-keeps-interior-overlap
requires: []
---

In `M=F_2^3`, the vector `(1,0,1)` and its two simple-Weyl conjugates
satisfy the coweight triangle because

```text
(1,0,1)+(1,1,0)=(0,1,1).
```

Therefore the translations by these vectors inside
`M rtimes SL_3(F_2)` satisfy exactly the same three-term diagonal relation as
the arithmetic coweights.  Adjoin commuting involutory lamps at the eight
points of `M`.  The linear group fixes the origin and transports the lamp at
the first translated point through its complete nonmonomial root orbit.

In the left regular representation, distinct lamp coordinates are balanced
independent commuting involutions, giving intersection trace `1/4` exactly.
Finally, direct multiplication in the affine group shows why the actual
dyadic scaling relation is absent: conjugating a nontrivial linear
transvection by a translation retains that transvection as its linear part,
whereas reduction modulo two of `e_12(2)` is trivial.  This proves both the
countermodel and the asserted boundary of its applicability.
