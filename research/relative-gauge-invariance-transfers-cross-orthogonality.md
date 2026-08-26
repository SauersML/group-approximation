---
rg: 2
id: relative-gauge-invariance-transfers-cross-orthogonality
kind: claim
title: One relative-gauge invariant payload projection transfers target cross-orthogonality back to the source
distinct_from:
  mixed-cross-zero-squares-have-four-state-gauge-model: that proves target orthogonality alone does not control source overlap; this identifies the exact additional relative-gauge defect spent by that model.
  returned-opposite-cross-zero-has-finite-s6-model: that satisfies every returned zero-product word by re-gauging the two Coxeter payloads; this gives a dimension-free inequality once one payload projection is authenticated against the relative gauge.
  separate-native-quarter-carrier-recovery: that asks for five native factor placements in two returned algebras; this reduces the remaining reservoir lock to invariance of one selected payload projection under one literal relative branch word.
  two-mixed-pauli-commutators-lock-the-relative-reservoir-gauge: that puts an exposed relative unitary near the Pauli commutant; this converts that conclusion into a source-versus-target projection-overlap estimate.
---

**ESTABLISHED DIMENSION-FREE REDUCTION.**  Let `P_0,P_1` be projections in
a finite tracial von Neumann algebra, let `U_0,U_1` be unitaries, and put

```text
Q_i=U_iP_iU_i^*,                 V=U_0^*U_1.           (RGI1)
```

Then

```text
||P_0P_1||_2
 <= ||Q_0Q_1||_2
    +min(||VP_1V^*-P_1||_2,||V^*P_0V-P_0||_2).        (RGI2)
```

Indeed, unitary invariance of the tracial `L^2` norm gives

```text
||Q_0Q_1||_2=||P_0VP_1||_2=||P_0VP_1V^*||_2.
```

Therefore

```text
P_0P_1=P_0VP_1V^*+P_0(P_1-VP_1V^*)
```

and contraction by `P_0` proves the first bound in `(RGI2)`.  Conjugating
the target product by `U_1` instead gives

```text
||Q_0Q_1||_2=||V^*P_0VP_1||_2,
```

and the same triangle inequality proves the second bound.

Thus the surviving payload lock after the returned `A_2` fold window is only
one explicit finite-coordinate estimate: authenticate either child payload
projection as approximately invariant under the relative branch word `V`.
No reconstruction of the full multiplicity algebra and no irreducibility
theorem is needed after that estimate is available.

For a Pauli payload this estimate is already reduced to two scalar word
defects.  If `X,Z` are exact anticommuting Pauli involutions and
`P_1 in W^*(X,Z)`, then
`two-mixed-pauli-commutators-lock-the-relative-reservoir-gauge` supplies a
unitary `W in {X,Z}'` with

```text
||V-W||_2<=||[V,X]||_2+||[V,Z]||_2.                  (RGI3)
```

Since `W` commutes with `P_1`, two triangle inequalities give

```text
||VP_1V^*-P_1||_2
 <=2(||[V,X]||_2+||[V,Z]||_2).                       (RGI4)
```

Combining `(RGI2)` and `(RGI4)` yields the completely explicit sufficient
boundary

```text
||P_0P_1||_2
 <=||Q_0Q_1||_2+2||[V,X]||_2+2||[V,Z]||_2.           (RGI5)
```

Thus after a literal mixed row exposes the same relative word `V` on the
same selected carrier, exactly two native Pauli commutators suffice; no
five-factor algebra reconstruction is needed for this overlap transfer.

The term is load bearing.  In the exact four-state gauge model,
`U_0=1`, `U_1` swaps `e_2,e_4`, and

```text
P_1=proj<e_2,e_3>,       VP_1V^*=proj<e_4,e_3>.
```

Hence `Q_0Q_1=0` while `P_0P_1` has rank one, and the relative-gauge term in
`(RGI2)` is nonzero.  Likewise the returned `S_6` model spends the defect by
moving a child Coxeter triple to a disjoint triple.  Equality of fold
outputs, returned cross-zero words, and finite Coxeter covariance do not
bound this term.

Consequently a successful literal row need not somehow assert that an
entire payload block is irreducible.  It is enough to couple `U_0^*U_1` to
one word-visible payload projection with a dimension-independent
normalized-HS invariance estimate.  The known exact models show that some
control of this relative reservoir gauge, or an equivalent positive charge
for its motion, cannot simply be omitted.

DERIVATION
relative-gauge-invariance-cross-orthogonality-proof
