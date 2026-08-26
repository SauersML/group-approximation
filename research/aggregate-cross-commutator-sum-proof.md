---
rg: 2
id: aggregate-cross-commutator-sum-proof
kind: route
title: Multiply the two-arm row and column nilpotents and realize their gauge in S6
target: aggregate-cross-commutator-sum-has-finite-s6-gauge
requires:
  - stabilized-cross-braid-has-s3-square-gauge-fence
  - signed-hecke-normalizer-has-eight-external-root-returns
---

The row supports in `X` make `X^2=0`, and the column supports in `Y` make
`Y^2=0`.  The reverse product is zero because the terminal index `8` of
both column arms is different from the initial index `7` of both row arms.
The forward product has exactly the two matched paths

```text
(7,9)(9,8)       and       (7,10)(10,8),              (ACSP1)
```

so it is `(pr+rp)E_78`.  Since `pr=q_0`, `rp=q_1`, and
`q_0+q_1=1`, this proves `(ACS3)`.  Expanding
`(1+X)(1+Y)(1+X)(1+Y)` with the vanishing products proves `(ACS4)`.

For the finite model, direct cycle multiplication gives

```text
alpha beta=(1 2 3 4)(5 6).                            (ACSP2)
```

Both `alpha,beta` are involutions, hence their commutator is the square of
`(ACSP2)`, namely `(1 3)(2 4)=E`.  Finally
`D=(1 3)(2 5)` and `E` share the transposition `(1 3)`; the remaining
factors multiply to the three-cycle `(2 4 5)`.  This verifies
`(ACS6)--(ACS7)` and the scoped gauge fence.
