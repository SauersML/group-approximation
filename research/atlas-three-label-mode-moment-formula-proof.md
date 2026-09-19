---
rg: 2
id: atlas-three-label-mode-moment-formula-proof
kind: route
title: Expand transported letters across three orthogonal label sectors
target: atlas-three-label-mode-two-unitary-moment-reduction
requires:
  - atlas-full-relator-data-factor-through-double-commutant-gauge
---

The projections in `(TLM1)` are nonzero, orthogonal, and sum to one.  Hence
`(TLM2)` is unitary.  Multiplication on the right by `I tensor V_0^*`
commutes with every untransported second-chart matrix and gives `(TLM3)`
without changing that transported chart.

For one second-chart letter,

```text
U_Z(lambda(b) tensor I)U_Z^*
 =sum_(p,q=0)^2 P_p lambda(b) P_q tensor Z_p Z_q^*.   (TLMP1)
```

Insert `(TLMP1)` at each of the `l` second-chart positions in `(TLM4)` and
distribute.  This is exactly `(TLM5)`--`(TLM6)`.  Since `pi_(U_Z)(s)` is
unitary,

```text
||pi_(U_Z)(s)-I||_2^2
 =2-2 Re tr(pi_(U_Z)(s)).                             (TLMP2)
```

The tensor-product trace of `(TLM6)` yields `(TLM7)`.

Finally, write the `(x,y)` block as

```text
(U_Z)_(x,y)=sum_(j=0)^2 (P_j)_(x,y) Z_j.              (TLMP3)
```

The three coefficient vectors `((P_j)_(x,y))_(x,y)` are linearly
independent because the nonzero orthogonal projections `P_j` are linearly
independent as label matrices.  Coordinate functionals on the finite block
array therefore recover each `Z_j` as a scalar linear combination of the
blocks in `(TLMP3)`.  This proves `(TLM8)`.
