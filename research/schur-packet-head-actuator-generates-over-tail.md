---
rg: 2
id: schur-packet-head-actuator-generates-over-tail
kind: claim
title: A Schur packet can use the Toeplitz head actuator and generate the full group over its compressed child
artifacts:
  - experiments/schur_packet_toeplitz_head_actuator.py
distinct_from:
  schur-child-crosses-toeplitz-compressor: that places the child in the compressed group and one full-packet generator outside it; this additionally makes that generator the bounded head actuator which generates the entire uncompressed coefficient ring.
  toeplitz-tail-plus-one-swap-generates: that supplies the ring actuator without a Schur packet; this incorporates the actuator as the packet's missing Pauli generator while preserving the full finite multiplication table.
---

Fix a Schur--Clifford packet `A_f<=B_f` with extra generators
`p_m,q_m`, and put `B_f^Q=<A_f,q_m>`.  For the Toeplitz ring

```text
T=F_2<x,y | yx=1>,       sigma(a)=xay+eps(a)f,
```

let `s` be the head swap from `(TSG1)` and let
`e_2=sigma^2(f)`.  Then, after increasing the elementary rank, there is a
faithful embedding

```text
iota:B_f -> Gamma=EL_r(T)                                (SAT1)
```

such that

```text
iota(B_f^Q) <= alpha(Gamma)=EL_r(sigma(T)),
Gamma=<alpha(Gamma),iota(B_f)>.                           (SAT2)
```

Thus the missing packet generator is not merely outside the compressed
group: it actuates the entire finite head over the tail.

This still does not prove a positive-density Reynolds wall.  In a matrix
representation the remaining action of `alpha(Gamma)` can act irreducibly on
the packet multiplicity and erase the local Reynolds density.  The theorem
removes the algebraic generation problem and leaves precisely that analytic
residual-action alternative.
