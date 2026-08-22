---
rg: 2
id: adjoint-parity-loewner-cone-proof
kind: route
title: Compare even-parity character projections before evaluating a vector state
target: adjoint-parity-cone-lifts-to-loewner-order
requires: []
---

Inside one check, the involutions `Ad(Q_k)` commute and their product is
`I`.  Their joint spectral decomposition is therefore supported on sign
strings with an even number of minus signs.  On each such character atom,
the indicator that coordinate `i` is negative is at most the sum of the
negative indicators at the other coordinates.  Since `P_k` is exactly that
negative-sign spectral projection, comparison on every joint atom proves
`(APL2)` in Loewner order.

For any `v in L_2(M)`, the numbers

```text
x_i(v)=<v,P_i v>
```

therefore lie in the Tanner fundamental cone.  If `(APL3)` holds for all
scalar vectors in that cone, then

```text
<v,P_i v> <= (1/(kappa L)) sum_k <v,P_k v>
```

for every `v`.  This is equivalent to the positive-operator inequality
`(APL4)`.  Finally,

```text
||Q_iQ_j-Q_jQ_i||_2^2
 =||(I-Ad(Q_i))Q_j||_2^2
 =4 <Q_j,P_i Q_j>,                                       (APL7)
```

so evaluating `(APL4)` at `v=Q_j` proves `(APL5)` without any centrality,
irreducibility, or simultaneous spectral-decomposition assumption.

For completeness, write `x_(i,j)=||[Q_i,Q_j]||_2^2`.  From `(APL5)` and
symmetry, for fixed `i,j`,

```text
sum_k x_(i,k) >= kappa L x_(i,j),
sum_l x_(k,l) >= kappa L x_(i,k)  for every k.
```

Summing the second inequalities over `k` and using the first gives

```text
sum_(k,l)x_(k,l) >= kappa^2 L^2 x_(i,j),                 (APL8)
```

which is `(APL6)`.
