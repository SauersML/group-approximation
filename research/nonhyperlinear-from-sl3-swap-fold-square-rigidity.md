---
rg: 2
id: nonhyperlinear-from-sl3-swap-fold-square-rigidity
kind: route
title: Contradict the second canonical fold moment with defect-only Gram idempotence
target: non-hyperlinear-group
requires:
  - sl3-swap-extension-has-defect-only-fold-square-rigidity
  - canonical-arithmetic-swap-fold-gram-is-arcsine
  - arithmetic-double-swap-extension-is-binary-coset-wreath
---

If the arithmetic double were hyperlinear, its binary swap extension `E`
would have canonical normalized-Hilbert--Schmidt microstates.  Apply the
defect-only fold-square claim to those assignments.  Their presentation
defect tends to zero, so `(SFS1)` gives

```text
tr(Q_nP_nQ_n-(Q_nP_nQ_n)^2)->0.                         (SFR1)
```

But the established canonical principal-angle law gives

```text
tr(Q_nP_nQ_n-(Q_nP_nQ_n)^2)->1/16.                      (SFR2)
```

This contradiction excludes canonical microstates of `E`.  The explicit
two-fold arithmetic amalgam is a subgroup of index two in `E`, and the
swap-extension theorem transfers hyperlinearity in both directions.
Therefore that finitely presented arithmetic double is non-hyperlinear.
