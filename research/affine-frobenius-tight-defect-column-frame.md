---
rg: 2
id: affine-frobenius-tight-defect-column-frame
kind: claim
title: Make each Frobenius incidence defect row a scaled partial isometry
distinct_from:
  affine-frobenius-algebraic-projection-crt: that asks directly for an arbitrary algebraic projection solving the right-ideal prescriptions; this asks for a stronger explicit cubic frame identity which manufactures the minimal projection by a fixed polynomial.
  algebraic-selector-mixing-frame-collapses-forbidden-sector: that combines a universal selector frame with exact mixing and thereby kills a forbidden sector in every representation; this frame is variable-specific, interpolates prescribed incidence columns, and is required only in the common complete BCS model.
---

**OPEN.**  For each source variable `x`, correlate the fixed
affine-Frobenius context packets so that their incidence columns

```text
X_x=(q_(c,x))_c,
Y_x=(A_(c,x)q_(c,x))_c,
D_x=X_x-Y_x                                           (AFT1)
```

satisfy both compatibility `(SIC3)` and, for one positive rational scalar
`lambda_x`,

```text
D_x D_x^* D_x=lambda_x D_x.                           (AFT2)
```

The construction must preserve the fixed context PVMs and the strict
weighted canonical deficit budget of
`rowwise-hecke-crt-certificate-for-nonce-bcs`.

Then the finite-support coefficient

```text
p_x=lambda_x^(-1)D_xD_x^*                             (AFT3)
```

is automatically the required projection in `(AFPC2)`.  Unlike the von
Neumann support projection, `(AFT3)` uses only multiplication, involution,
addition, and a scalar inverse, so it remains in the algebraic group ring.

## Attempts

1. **Normalize the analytic support projection.**  Functional calculus
   gives the support of `D_xD_x^*`, but does not imply the finite cubic
   identity `(AFT2)` or finite group support.
2. **Add a free Julia complement.**  This can complete one contraction to a
   symmetry but does not force the singular values of the already prescribed
   defect row to be all equal.  The stabilized projection CRT remains.
3. **Use a universal finite Weyl tight frame.**  A frame independent of the
   incidence data either acts only in an external matrix coordinate or falls
   under the existing selector-mixing collapse.  What is required is a
   correlated, variable-specific frame whose columns are exactly `(AFT1)`.
4. **Repeat columns to tune weights.**  This permits integer weighting and
   may equalize the nonzero singular values, but no construction is known
   which also preserves all pairwise compatibility equations and the strict
   Frobenius deficit.

The remaining target is a finite packet relation that makes the prescribed
incidence defect row a scaled partial isometry without forcing an affine
global section or destroying the canonical deficit.
