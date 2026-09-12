---
rg: 2
id: atlas-q14-thirteenth-double-coset-proof
kind: route
title: Commute the two half-rank involutions and classify their joint sectors
target: atlas-q14-adds-stratified-thirteenth-double-coset
requires:
  - atlas-common-u-is-twelve-double-coset-system
  - atlas-q14-forces-t30-covariance-floor
  - atlas-charts-overlap-trivially
  - atlas-word-19243-is-kernel-relation
---

Since `h=RaR^*` and `V=WR^*`, one has

```text
VhV^*=WaW^*.
```

Substitution in the established aligned q14 formula proves `(QDC2)` and then
`(QDC3)`.

Put `b=WaW^*`.  Both `a` and `b` are involutions.  The elementary identity

```text
(ab)^2=1 iff ab=ba
```

shows that q14 is exact precisely when their two spectral projections
commute.  Both negative projections have rank `n=D/2`.  If their intersection
has dimension `m`, simultaneous diagonalization forces the four dimensions
in `(QDC4)`.  Conversely those four sectors define commuting balanced
involutions.  The centralizer `C_a=U(n)xU(n)` acts transitively on the choices
of subspaces with fixed four dimensions, on both the source and target side.
This is exactly the double-coset classification `(QDC5)`.

Equation `(QDC6)` follows because the gauge changes neither product `X_eRY_e`
nor `W`.  Hence no word depending only on the common represented charts can
select a factorization witness inside that fiber.

Equation `(QDC7)` is the same substitution `VhV^*=WaW^*`; `(QDC8)` is then
the established q14 root estimate without any change of constants.

For the final escape, form the displayed quotient group.  Its defining
relators map to one in the binary-Leavitt target, while trivial chart overlap
in that target proves injectivity and trivial intersection of the two chart
copies in the quotient.  The canonical trace restricts to the regular trace
on each finite chart.  Two trace-preserving copies of the same finite
dimensional algebra in a finite factor are unitarily conjugate, giving the
claimed common frame.  This proves only a finite-tracial escape, not a matrix
escape, exactly as required by the CE-sensitive qualifier.
