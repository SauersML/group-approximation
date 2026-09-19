---
rg: 2
id: endpoint-order-five-full-hecke-source-return-proof
kind: route
title: Audit the endpoint actor against all ten generators of the common Hecke source
target: endpoint-order-five-return-leaves-full-hecke-fine-sign-free
requires:
  - endpoint-order-five-actor-has-half-gram
  - center-chain-mixed-hecke-overlap-is-common-pauli-source
---

Use the literal four-projective-summand block `(OFG5)`.  The requirements
from `C_2,C_3,v,w,s` first restrict a signed-source return to
`diag(1,GL_3(F_2))`.  The extra roots `d,f,c,k` distinguish the depth-two
and depth-three target incidences.  The remaining nonidentity block action
fixes the `C_3,s,s'` root coordinates and sends `t` to `ts'`.  Breadth-first
words in the exact finite actor give the shortest representative `(OQF2)`.

Conjugate each of

```text
C_1,C_2,C_3,d,f,c,k,v,w,s,t,s'
```

by that representative using faithful binary-prefix Leavitt normal forms.
The first ten images are the original generators, while the last two are
exactly `(OQF3)`.  Since the three negative generators are fixed as well,
the signed character is fixed and hence `RQ=QR`.

On the `Q` compression, the remaining relation is the standard Pauli
covariance `XtX=ts'`.  Assigning `(s',t,R)=(-I,Z,X)` proves `(OQF4)`.
The endpoint identity `WsW=s'` then proves `(OQF5)`.

For the separate full-cell screen, enumerate shortest words in the 168
element signed-`K_1` return subgroup whose four-bit action sends `s` to
`t`.  The first word is `(OQF6)`.  Exact conjugation of the complete
`A_1,A_2,B_2,B_3,J_1,J_2` packet gives `(OQF7)` and the displayed support
of the `J_1` conjugate, proving the occurrence fence without a trace or
representation argument.

`experiments/endpoint_fine_collision_odd_mixed_audit.py` reproduces every
displayed conjugate.  It is run only through MSI and avoids collecting the
full 8192-element source group; exact images of the ten named generators
already decide pointwise return.
