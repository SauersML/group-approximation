---
rg: 2
id: binary-jacobson-untyped-decoder-audit-proof
kind: route
title: Apply the sparse Toeplitz inequality and use vacuity in the converse
target: binary-jacobson-untyped-square-decoder-is-target-equivalent
requires:
  - positive-toeplitz-head-is-square-defect-or-rectangular-escape
---

If a surviving sequence and data `(JUC1)` existed, put

```text
delta_n=||Y_nX_n-C_n||,       eta_n=||P_n-(C_n-X_nY_n)||.
```

The operator-norm clause of the prerequisite gives, for all large `n`,

```text
1=||P_n|| <= eta_n+delta_n/(1-delta_n),                (1)
```

whose right side tends to zero.  Thus the untyped decoder assertion implies
that no surviving sequence exists.  Conversely, if no surviving sequence
exists, the universal assertion about data attached to every surviving
sequence is vacuous.  This proves equivalence.

The proof uses none of the group presentation beyond the name of the marked
word.  That is precisely why occurrence typing and a relator-defect modulus
are required before a decoder can count as progress toward the target.
