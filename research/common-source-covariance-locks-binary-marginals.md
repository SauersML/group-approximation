---
rg: 2
id: common-source-covariance-locks-binary-marginals
kind: claim
title: Common-source covariance locks binary endpoint marginals with linear HS loss
distinct_from:
  capacity-gated-common-corner-bcs-two-cell: that controls all source commutators and BCS residuals; this is the elementary trace estimate converting its common-source rows into the two marginal equalities in RNS1.
  rank-one-no-signaling-pairing-floor: that derives a failure floor from supplied equal marginals; this supplies those equalities from compressed covariance.
  global-covariance-misses-capacity-compression: that shows a global row does not imply compressed covariance; this assumes the correctly compressed common-source rows have been constructed.
---

Let `Q` be a projection in a finite tracial matrix algebra.  For context
indices `c`, let

```text
V_c^*V_c=Q,
A_(c,x)=A_(c,x)^*=A_(c,x)^(-1),
Z_x=Z_x^*=Z_x^(-1),
D_(c,x)=A_(c,x)V_c-V_cZ_x.                              (CSM1)
```

Write `P(U)=(1+U)/2`.  Then

```text
|tau(V_c^*P(A_(c,x))V_c)-tau(QP(Z_x))|
 <=(1/2)||D_(c,x)||_2.                                  (CSM2)
```

Consequently, if contexts `c,c'` use the same endpoint word `Z_x`, their
transported binary marginals satisfy

```text
|tau(V_c^*P(A_(c,x))V_c)-tau(V_(c')^*P(A_(c',x))V_(c'))|
 <=(1/2)(||D_(c,x)||_2+||D_(c',x)||_2).                 (CSM3)
```

The same estimates hold with the Gram, involution-rounding, and word
telescoping errors added linearly.

These are the unnormalized `Q`-weighted marginals used in the integrated
failure ledger.  If `tau(Q)>0`, the corresponding conditional marginals are
obtained by dividing `(CSM2)--(CSM3)` by `tau(Q)`; no such division is needed
when the inequalities are summed over forbidden fibers.

If the rounded target observables in one context commute and `F_c(A_c)` is
one of its forbidden joint spectral projections, then

```text
tau(V_c^*F_c(A_c)V_c)=||F_c(A_c)V_c||_2^2.              (CSM4)
```

Thus target-context residual energy controls the convention-failure mass on
the same source.  Applying `(CSM3)` to the `X` endpoint in contexts `00,01`
and the `Y` endpoint in contexts `01,11` gives exactly `(RNS1)` up to
`O(sqrt(E_cov))` in its integrated `Q`-weighted form; `(CSM4)` charges the
three convention failures to `E_tar`.  No equality of multiplicity bases is
assumed beyond the literal common Gram source `Q`.
