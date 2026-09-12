---
rg: 2
id: raw-schur-generator-is-not-child-center
kind: claim
title: The raw last Clifford generator does not label the Schur child simples
invalidates:
  - toeplitz-schur-bcs-shift-amalgam-proof
  - fixed-scale-holonomy-via-reset-schur-atlas
distinct_from:
  schur-rank-output-is-not-a-scalar-selector: that rules out reading the nonlinear rank bit as a selector word; this identifies the more immediate error that the raw child generator does not even commute with the baseline packet.
  controlled-central-phase-finite-group-barrier: that obstructs a finite overgroup realizing a nonlinear controlled commutator; this computes the actual central child coefficient which must be groupified.
---

For the Schur matrix

```text
M_f(x)=[[U_f(x),e_t],[e_s^T,0]],
```

let `A_f` be the leading packet and let
`B_f^Q=<A_f,q_(N+1)>`. In the marked `J=-1` sector,

```text
[p_t,q_(N+1)]=J=-1.                                  (RSC1)
```

Therefore raw `q_(N+1)` does not commute with `A_f`, its eigenspaces are not
`A_f`-submodules, and its spectral multiplicities are not the multiplicities
of the two child simples in `(OCB1)`.

The actual relative child-center involution in the finite group algebra is

```text
Q_f=sum_x e_x Q_x,
Q_x=q_(N+1) product_j q_j^(v_j(x)),
v(x)=U_f(x)^(-1)e_t,                                  (RSC2)
```

where `e_x` is the central selector idempotent. It commutes with `A_f`, and on
a violating sector its signs distinguish the two `B_f^Q` simples. In general
`v(x)` is nonlinear, so `(RSC2)` is a selector-controlled additive
group-algebra coefficient, not one uniform group word.

Consequently a reset gadget controlled by the *raw spectral projections* of
`q_(N+1)` balances the wrong decomposition.  This does not prevent an
ordinary automorphism from acting correctly on the child types:
`schur-child-center-sign-flip-is-group-automorphism` proves that
`q_(N+1)->Jq_(N+1)` fixes `A_f` and sends the corrected coefficient
`Q_f->JQ_f`.  A valid recurrence may therefore exchange the two corrected
branches without exposing `Q_f` as a group word.  It must still reset or
transport the old selector character, which that automorphism fixes.
