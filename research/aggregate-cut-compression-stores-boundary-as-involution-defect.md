---
rg: 2
id: aggregate-cut-compression-stores-boundary-as-involution-defect
kind: claim
title: Block compression stores the aggregate-cut boundary exactly as involution defect
distinct_from:
  regularized-anchor-square-function-has-dimension-free-cut: that constructs the approximately reducing aggregate cut; this carries its leakage into an exact positive defect identity without reflection rounding.
  spectral-cut-anchor-reset-pays-boundary-in-one-row: that resets the anchor while leaving the other generators nonreducing; this block-compresses every other generator to obtain an exactly reducing contraction tuple.
  one-anchor-grading-makes-parity-damage-quadratic: that assumes reflection inputs and studies odd-term cancellation; this preserves the soft odd row for selfadjoint contractions and postpones reflection rounding until after correction.
---

ESTABLISHED.  Let `A,B_1,...,B_L` be reflections and let `p` be a
projection commuting with `A`; put `q=1-p`.  Replace each site reflection
by its block compression

```text
 X_i=pB_ip+qB_iq.                                      (ACS1)
```

Then `X_i` is a selfadjoint contraction commuting with `p`, and the
following identities are exact:

```text
 I-X_i^2=pB_iqB_ip+qB_ipB_iq >=0,                      (ACS2)
 ||B_i-X_i||_2^2=tau(I-X_i^2)=||[p,B_i]||_2^2.         (ACS3)
```

Thus, with `D(p)=L^(-1)sum_i||[p,B_i]||_2^2`, both the average squared
movement and the average involution residual are exactly `D(p)`.

If

```text
 Y_i=(B_i-AB_iA)/2,       K=L^(-1)sum_iY_i^2,
 Z_i=(X_i-AX_iA)/2,
```

then on the retained block

```text
 qZ_iq=qY_iq,
 (1/L)sum_i(qZ_iq)^2 <=qKq.                            (ACS4)
```

In particular, the regularized aggregate cut `(RAC6)` gives the exact
row-column estimate

```text
 (1/L)sum_i(qZ_iq)^2<=2theta q                         (ACS5)
```

for an exactly `p`-reducing tuple.  No sign or polar correction has been
made, so no new operator-norm spike can appear.

Fixed-width word defects remain quantitatively controlled.  If `w` has
length at most `m`, telescoping for contractions gives

```text
 ||w(X)-w(B)||_2^2<=m sum_(occurrences i in w)||X_i-B_i||_2^2.  (ACS6)
```

Consequently every bounded-degree, fixed-width parity layer pays only
`O_m(D(p))` after the block compression.  The complete-pair dense
quadratic terms are governed by `(ACS5)` rather than by individual operator
norms.

This reduces the aggregate-cut leakage gate to a precise analytic
extension: run the row-column Newton correction on selfadjoint contractions
while including the positive residuals `I-X_i^2` in its energy.  Reflection
rounding may be postponed until this augmented energy has converged; for a
selfadjoint contraction `X`, functional calculus gives
`||sgn(X)-X||_2^2<=tau(I-X^2)`.  What remains unproved is that the existing
linearized gap and nonlinear contraction persist for this augmented
contraction system.
