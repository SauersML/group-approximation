---
rg: 2
id: one-round-v4-lamp-wordization-proof
kind: route
title: Orthogonal answer corners furnish the V4 lamp representation
target: one-round-v4-lamps-wordize-a-bcs-losing-projection
requires: []
---

For every `a`, the two operators in `(VL3)` are commuting self-adjoint
involutions.  For distinct `a,a'`, all their nonidentity parts have
orthogonal supports `P_aH,P_a'H`, so the images of the distinct `V_4`
factors commute.  Thus `(VL3)` is a representation of the finite group
`V_Omega`.

On `P_cH`, the word `(VL4)` is `-1` when `c in F`, is `B` when
`c notin F` and `s(c)=1`, and is `-B` when `c notin F` and `s(c)=-1`.
Consequently it is

```text
-sum_(c in F)P_c + sum_(c notin F)s(c)P_cB
 = 1-2L_(F,s,B).
```

This proves `(VL5)`.  In the canonical answer-basis model, permutation of
the basis conjugates the `a`-th pair of lamps to the corresponding permuted
pair, so the same representation extends to the stated wreath product.
