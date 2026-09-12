---
rg: 2
id: aggregate-binary-whitehead-factorization-proof
kind: route
title: Split the aggregate opposite-root word into two commuting S3 cells
target: aggregate-binary-whitehead-does-not-read-completeness
requires:
  - outer-root-leavitt-table
---

Roots with a common initial index commute, as do roots with a common terminal
index.  The two cross pairs in `(ABW3)` are composable, but their Steinberg
coefficients are `t_0s_1` and `t_1s_0`, which vanish.  This proves all four
commutations in `(ABW3)`.

For fixed `i`, the pair `s_i,t_i` satisfies `t_is_i=A`.  Direct multiplication
in the `(1,6+i)` block gives

```text
X_iY_iX_i=Y_iX_iY_i
 =[[1+s_it_i,s_i],[t_i,0]],                            (1)
```

so `(ABW4)` uses only the matching inverse row.  Expand `RLR`, commute every
factor belonging to branch zero past every factor belonging to branch one,
and apply `(ABW4)` twice.  This is exactly `(ABW5)` and proves that `(ABW6)`
is absent.

For the finite model, in each `S_3` choose the transpositions `(1 2)` and
`(2 3)`.  They obey the braid, and elements in different direct factors
commute.  Hence `(ABW3)--(ABW5)` hold.  The independent Klein-four factor
satisfies `C_0C_1=J` with `J` nonidentity.  Its left regular representation
has zero defect on the displayed table and
`||lambda(J)-1||_op=2`.

