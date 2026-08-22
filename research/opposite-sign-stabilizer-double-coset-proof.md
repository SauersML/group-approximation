---
rg: 2
id: opposite-sign-stabilizer-double-coset-proof
kind: route
title: Move both tensor factors by the fatal holonomy
target: opposite-sign-stabilizer-double-coset-collapses-coinvariant-pairing
requires: []
---

Write `(OSD3)` as

```text
p_0=h_X p_1 h_Z,          h_X in H_X, h_Z in H_Z.         (OSP1)
```

In diagonal coinvariants one may move both tensor factors by `h_X^-1`.
Using `h_X^-1 x=x` and then `(OSP1)` gives

```text
[x tensor p_0 z]
 = [x tensor h_X p_1 h_Z z]
 = [h_X^-1 x tensor p_1 h_Z z]
 = [x tensor p_1 z].                                      (OSP2)
```

Here the last equality uses `h_Z z=z`.  Hence `c_0=c_1`.  Applying any
linear functional on the coinvariant tensor module gives equal values on
the two classes, proving that `(OSD4)` is impossible.

For the path formulation, `(OSD5)` implies

```text
[x tensor p_1 z]
 = [a x tensor a p_1 z]
 = [x tensor p_0 z],                                      (OSP3)
```

directly from the defining diagonal-coinvariant relation.  Conversely,
`(OSP1)` supplies the transporter `a=h_X`, since
`h_X p_1 z=p_0 h_Z^-1 z=p_0 z`.  The double-coset and holonomy
formulations are therefore the same obstruction.

Finally, `(OSD6)` is necessary for opposite signs: if the two double cosets
intersect, write

```text
h_0 p_0 k_0=h_1 p_1 k_1
```

with `h_b in H_X,k_b in H_Z`.  Rearrangement puts `p_0` in
`H_X p_1 H_Z`, and the preceding calculation applies.
