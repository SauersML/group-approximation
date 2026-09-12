---
rg: 2
id: full-fold-compose-return-closes-code
kind: route
title: Close the chromatic code by composing the full fold through both binary arms
target: binary-leavitt-bounded-area-chromatic-code
requires:
  - full-completeness-opposite-menu-has-finite-gl5-fusion
---

**INVALIDATED COMPOSABLE-FOLD CELL.**  Do not stop at the common-root
equality `C_0C_1=J`.  For each branch, right-compose that equality with the
same named `s_j` occurrence, and then left-compose the result with the same
named `t_i` occurrence.  The desired table is

```text
[C_i,S_j]=delta_(ij)R_j,       [J,S_j]=R_j,
[T_i,R_j]=delta_(ij)J.                                  (FFR1)
```

Thus the matching two-step loop returns through `t_js_j=A`, while both
crossed loops vanish.  This is the smallest bounded output-root word which
tests the fold, both branches, and the same two occurrences after the fold.

`full-fold-compose-return-has-finite-affine-model` gives an exact finite
marked model of `(FFR1)`, including equivariant finite payload/opposite-root
packets over every label used in the calculation.  The loop defeats the
three-character `S_3` specialization, but a four-bit affine specialization
survives.  Hence composability of the folded outputs is still not a
same-matrix-corner decoder.

