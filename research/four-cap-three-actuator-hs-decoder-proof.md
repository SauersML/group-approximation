---
rg: 2
id: four-cap-three-actuator-hs-decoder-proof
kind: route
title: Transfer affine-Leavitt root collapse through the marked D8 commutator
target: four-cap-three-actuator-hs-packet-blocker
requires:
  - four-cap-three-actuator-destroys-all-fd-packet-evaluations
  - affine-leavitt-steinberg-hs-coefficient-decoder
  - approximate-relative-leavitt-cell-kills-active-trace
---

Apply the decoder and the relative-Leavitt trace inequality to the
restriction of a `Gamma_3` microstate to the fixed `Gamma_A` generators.
Equations `(ALD1)--(ALD2)` give `(THB2)` with a dimension-independent
modulus.  Evaluation of the fixed D8 relator differs from the identity by
at most the presentation defect.  For unitaries `W,S`,

```text
||W S W^* S^*-I||_2
 <= ||(W-I)S W^* S^*||_2+||S(W^*-I)S^*||_2
 =2||W-I||_2.                                           (TAP2)
```

Take `W=w(U)` and `S=s(U)` to obtain `(THB3)`.  Since
`q=(1-J)/2`, the second inequality of `(THB1)` is immediate.
