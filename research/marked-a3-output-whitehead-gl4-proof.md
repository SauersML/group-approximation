---
rg: 2
id: marked-a3-output-whitehead-gl4-proof
kind: route
title: Specialize the payload path and its opposite root inside GL4 over F2
target: marked-a3-output-whitehead-has-finite-gl4-model
requires: []
---

For an idempotent `q`, multiply the three elementary `(1,4)` blocks in
`(MAW1)`.  Characteristic two gives the displayed block in `(MAW2)`; another
block multiplication proves its square is one and its conjugation swaps the
two root directions.

For the finite model, the Steinberg multiplication rule over `F_2` gives

```text
[x_23(1),x_34(1)]=x_24(1),
[x_12(1),x_24(1)]=x_14(1),
[x_12(1),x_23(1)]=x_13(1),
[x_13(1),x_34(1)]=x_14(1),
```

which proves `(MAW4)`.  If `X=1`, both nested outputs are one.  On the
`(1,4)` coordinates, `ZLZ` is the transposition matrix, proving `(MAW5)`.
All matrices are invertible binary `4 by 4` matrices, so the generated group
is finite.  A nonidentity element has trace zero in its left regular
representation, which proves `(MAW6)`.

