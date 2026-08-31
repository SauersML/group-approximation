---
rg: 2
id: binary-jacobson-untyped-square-decoder-is-target-equivalent
kind: claim
title: An untyped Jacobson square decoder is equivalent to the MF-invisibility target
distinct_from:
  binary-jacobson-head-root-has-opnorm-square-decoder: that now requires fixed named occurrences and a relator-defect modulus; this proves why those semantic requirements are mandatory.
  positive-toeplitz-head-is-square-defect-or-rectangular-escape: that supplies the finite-matrix contradiction once square Toeplitz data exist; this audits the logical status of asserting those data for every surviving microstate without constructing them.
---

**ESTABLISHED AUDIT.**  Consider the assertion that every operator-norm
microstate sequence retaining `w_T=x_13(1-ST)` admits arbitrary
coordinate-dependent nonzero projections `P_n<=C_n` and contractions
`X_n,Y_n in C_nM_(d_n)C_n` satisfying

```text
||Y_nX_n-C_n||->0,
||P_n-(C_n-X_nY_n)||->0.                              (JUC1)
```

Without a requirement tying `C_n,P_n,X_n,Y_n` to named group-word
occurrences and bounding `(JUC1)` by explicit relator defects, this assertion
is equivalent to saying that no surviving microstate sequence exists.
Therefore it is equivalent to the Jacobson head MF-invisibility target and
is not an independent decoder lemma.

The valid intermediate target must additionally provide a fixed finite word
package, a specified finite-coordinate selection operation, and a
dimension-independent modulus from the defects of those words to `(JUC1)`.
