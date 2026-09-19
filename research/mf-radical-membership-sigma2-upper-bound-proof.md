---
rg: 2
id: mf-radical-membership-sigma2-upper-bound-proof
kind: route
title: Arithmetize marked norm-corona detection at every relator scale
target: mf-radical-membership-has-a-sigma2-upper-bound
requires:
  - universal-mf-quotient
  - countable-group-mf-conventions
artifacts:
  - GroupApproximation/Sofic/NormMFCoronaRadical.lean
  - GroupApproximation/Sofic/NormMFUniversalCorona.lean
  - GroupApproximation/Sofic/OperatorMFPairAmplification.lean
---

Let `D(P,w,n,d)` be the fixed-dimensional feasibility sentence

```text
there exist U_1,...,U_k in U(d):
  max_j ||r_j(U)-1|| <= eta_n,
  ||w(U)-1|| >= 1/2.
```

It is decidable by effective real-closed-field quantifier elimination.

If a norm-matrix-corona homomorphism detects `w`, lift the finitely many
generator images to unitary sequences.  Relator defects tend to zero and the
marked word stays a positive distance from one on a cofinal set.  Cairn's
pair/tensor amplification normalizes that positive distance to `1/2`, giving
`D(P,w,n,d)` at every scale.

Conversely choose one witnessing tuple for every `n`.  The generator sequences
define a free-group homomorphism into the norm corona; the relator defects tend
to zero, so it factors through `Carrier P`, and the uniform marked gap detects
`w`.  Hence nonmembership is `forall n exists d D`, a `Pi^0_2` predicate, and
membership is its `Sigma^0_2` complement.
