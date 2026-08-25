---
rg: 2
id: finite-order-root-corona-bott-proof
kind: route
title: Average the second lift into the commutant of an exact torsion lift
target: finite-order-root-cannot-carry-a-corona-bott-class
requires:
  - corona-commuting-torsion-lifts
  - matrix-corona-k0-index-survives
---

Use `corona-commuting-torsion-lifts` on the one-element family `{u}` to
choose a unitary lift `U_n` with `U_n^m=1` exactly.  Choose any unitary lift
`W_n` of `v`.  Since `u` and `v` commute in the quotient,

```text
||U_nW_n-W_nU_n|| -> 0.
```

Average over the finite cyclic action:

```text
X_n=(1/m) sum_(j=0)^(m-1) U_n^j W_n U_n^(-j).          (FRP1)
```

Then `X_n` commutes with `U_n` exactly and `||X_n-W_n||->0`.  Hence
`X_n^*X_n->1`; on a cofinite tail its polar part

```text
V_n=X_n(X_n^*X_n)^(-1/2)
```

is a unitary, still commutes with `U_n`, and differs from `W_n` by a
norm-null sequence.  Fill the finitely many early coordinates with the
identity.  This proves `(FRB1)`.

The pair `(U_n,V_n)` defines a homomorphism from `C(T^2)` to every matrix
coordinate.  A homomorphism from `C(T^2)` to a full matrix algebra sends the
reduced Bott class to zero: after simultaneous diagonalization it is a
finite direct sum of point evaluations, and the reduced Bott bundle has
virtual rank zero at every point.  Therefore every coordinate Bott index is
zero.  Passing to the product and then the corona gives zero in
`K_0(Q_d)=L(d)/(direct-sum Z)`.

