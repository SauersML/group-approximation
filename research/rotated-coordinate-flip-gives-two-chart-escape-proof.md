---
rg: 2
id: rotated-coordinate-flip-gives-two-chart-escape-proof
kind: route
title: Rotate the second coordinate PVM inside the diagonal actor commutant
target: two-sl3-shell-charts-have-a-rotated-flip-escape
requires:
  - two-equivariant-shell-pvms-have-independent-coordinate-escape
---

# Rotate the second coordinate PVM inside the diagonal actor commutant

Since `F=F^*=F^(-1)` commutes with the diagonal actor, so does `U_t`, and
`Q_i(t)` remains a covariant PVM.  Expanding `(RTF1)` gives

```text
Q_i(t)=cos(t)^2 Q_i+sin(t)^2 P_i
       +i sin(t)cos(t)(FQ_i-Q_iF).                       (RFP1)
```

For `i!=j`, the last term couples `delta_(j,i)` and `delta_(i,j)` while
`P_i` distinguishes those vectors.  Hence `[P_i,Q_i(t)]` is nonzero when
`sin(t)cos(t)` is nonzero.

Equation `(RTF2)` follows immediately from `U_t^*Q_i(t)U_t=Q_i` and
`FQ_iF=P_i`; `(RTF3)` follows by compression.  Both `F` and `U_t` commute
with `rho(C)`, proving `(RTF4)`.

Finally,

```text
tr(P_iQ_i)=1/42^2,       tr(P_i)=1/42.
```

The cross term in `tr(P_iQ_i(t))` vanishes, so `(RFP1)` yields `(RTF5)`.
All assertions are exact finite-dimensional identities.
