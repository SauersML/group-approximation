---
rg: 2
id: periodic-higman-spectrum-contains-three-proof
kind: route
title: An exact PSL2(11) order-three certificate
target: periodic-higman-spectrum-contains-three
requires: []
---

Work in `H=PSL_2(11)`, representing elements by determinant-one matrices
modulo the scalar subgroup `{+-I}`.  Put

```text
s  = [[4,8],[8,8]],
h0 = [[1,6],[5,9]],   h1 = [[2,7],[10,8]],
h2 = [[4,3],[4,6]],   h3 = [[3,2],[10,7]]              (mod 11),
```

and let `alpha=Ad(s)`.  Every displayed matrix has determinant one.  Direct
matrix multiplication modulo eleven verifies

```text
s h_i s^(-1)=[h_i,h_(i-1)]       for i in Z/4,
s^3=+-I,
```

while neither `s` nor `s^2` is scalar.  Thus `alpha` has projective order
three.  Closing the four displayed `h_i` under multiplication and inversion
enumerates all `660` elements of `PSL_2(11)`, so they generate `H`.  These
finite exact checks give a certificate for `3 in Sigma`.
