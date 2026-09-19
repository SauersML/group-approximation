---
rg: 2
id: binary-leavitt-null-prototype-necessity-proof
kind: route
title: Use the marked word itself and the zero coefficient tuple
target: binary-leavitt-three-row-compiler-needs-null-prototypes
requires: []
---

Let `r_U` be the rounded involution and

```text
p_U=(1-r_U)/2!=0.
```

On the range of `p_U`, the involution `r_U` acts as `-1`, hence

```text
||(r_U-1)p_U||_op=2.
```

If spectral rounding has error
`||z(U)-r_U||_op<=kappa`, then

```text
||z(U)-1||_op
 >=||(z(U)-1)p_U||_op
 >=||(r_U-1)p_U||_op-||(z(U)-r_U)p_U||_op
 >=2-kappa.                                           (NPP1)
```

For sufficiently accurate tuples `kappa<=1`, proving `(NPT2)`.  With the
four zero operators from `(NPT1)`, the two inverse-row defects and the
completeness-row defect are all `||p_U||_op=1`.  Choosing `q_1=z`, `C=1`,
and the empty address proves the literal `(BAC1)` condition.

The last assertion is syntactic: `z` is nontrivial in the presented group,
so it is not in the relator normal closure.  Thus this automatic prototype
cannot receive a fixed relator filling, exactly the hypothesis used by the
downstream telescoping argument.
