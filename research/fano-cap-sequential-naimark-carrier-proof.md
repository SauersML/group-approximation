---
rg: 2
id: fano-cap-sequential-naimark-carrier-proof
kind: route
title: Stack all sequential cap products into a rectangular tight frame
target: fano-cap-sequential-products-form-an-algebraic-naimark-carrier
requires:
  - fano-maximal-cap-overlap-has-positive-sequential-mass
  - tracial-cap-menus-are-central-core-partitions
---

For `(FNC3)`, expand

```text
sum K_boldlambda^* K_boldlambda
=r^(-m) sum
 E_(1,lambda_1)...E_(m,lambda_m)
 E_(m,lambda_m)...E_(1,lambda_1).
```

The two occurrences of `E_(m,lambda_m)` are adjacent.  Sum over `lambda_m`,
use idempotence and `(FNC1)`, and obtain a factor `r`.  Repeat inward through
`lambda_(m-1),...,lambda_1`.  The result is `1`.  Hence `V^*V=1`, so
`Q^2=VV^*VV^*=Q`, and `(FNC5)` is immediately a unital star homomorphism.

For `(FNC6)`, traciality and `(FNC3)` give

```text
sum_boldlambda ||K_boldlambda R||_2^2
=sum tau(R^* K_boldlambda^* K_boldlambda R)
=tau(R^*R).
```

Matrix-trace cyclicity gives `(FNC8)`.  The standard Wedderburn block of an
`N`-dimensional irreducible finite-group representation is `M_N(C)`, and
tensoring that block with `q C[Gamma]q` gives `(FNC9)`.  A nonzero algebraic
projection has positive canonical trace because
`tau(Q)=tau(Q^*Q)=||Q||_2^2` in the faithful group trace.

For one context, the `lambda` coordinate of `V` is `E_lambda/sqrt(r)`, so
compression of the external coordinate projection is exactly `(FNC10)`.
If `E_lambda/r` were a projection with `r>1`, idempotence would give
`E_lambda/r^2=E_lambda/r`, hence `E_lambda=0`.  Thus every nonzero cap label
is nonreducing.

For any two projections `Q,L`, direct expansion and traciality give

```text
||[Q,L]||_2^2=2 Tr(QL)-2 Tr(QLQL).
```

Insert `V^*L_lambda V=E_lambda/r` to obtain `(FNC11)`.  Summing over
`lambda` and using `sum_lambda E_lambda=r1` gives `(FNC12)`.

Finally, for projections `Q,L`, the compression `QLQ` is a projection in
`QMQ` only when `Q` and `L` commute.  Indeed

```text
QLQ-(QLQ)^2=QL(1-Q)LQ,
```

and vanishing of this positive operator gives `(1-Q)LQ=0`; taking adjoints
gives the other off-diagonal block.  Therefore turning the POVM effect into
a sharp branch forces reduction.  Multiplicative branch compression then
falls under the exact-compression argument of
`tracial-cap-menus-are-central-core-partitions`, proving the stated
boundary.
