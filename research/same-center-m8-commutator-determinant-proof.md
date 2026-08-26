---
rg: 2
id: same-center-m8-commutator-determinant-proof
kind: route
title: Compare determinants, count the free payload qubit, and test the braid in S3
target: same-center-m8-commutators-cannot-wordize-one-eighth-reflection
requires:
  - same-center-prefix-whiteheads-are-uncontrolled-adjacent-swaps
  - controlled-pauli-commutator-is-and-times-multiplicity-commutator
  - adjacent-prefix-whitehead-braid-conjugates-reservoir-gauges
  - packet-dressed-shared-implementer-requires-one-outer-class
---

For `A,B in U(8)`, multiplicativity of determinant gives

```text
det([A,B])
 =det(A)det(B)det(A)^(-1)det(B)^(-1)=1.               (1)
```

The reflection `C_(1/8)=1-2E` has eigenvalue `-1` once and eigenvalue `+1`
seven times, hence determinant `-1`.  Equations `(1)` and `(MCO3)` prove
that it is not a two-word label commutator.

For the controlled-Pauli specialization, the two half-controls fix one
joint basis value of the first two qubits but do not cut the third qubit.
Their intersection therefore has dimension two.  Applying the exact
controlled-AND commutator identity gives `1-2PQ`, with two negative
eigenvalues and negative fraction `1/4`.  Cutting that remaining factor to
dimension one would require a joint control already present in one input
gate, which is the desired one-eighth occurrence itself.

Finally the Whitehead braid gives the same Coxeter relation on `V_1,V_2`.
Take `V_1=(12)` and `V_2=(23)` in the permutation representation of `S_3`.
They are involutions and satisfy the braid, but

```text
[V_1,V_2]=(V_1V_2)^2 !=1.                              (2)
```

Thus braid conjugacy cannot discharge the multiplicity commutator in the
controlled-Pauli factorization.  Reusing one literal implementer instead is
covered by the outer-class theorem: it cannot realize the two distinct
controlled symplectic actions.  These three calculations prove the scoped
fence and leave only the new mixed occurrence or identity-outer anchor
listed in `(MCO9)`.
