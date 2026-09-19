---
rg: 2
id: diagonal-hnn-exactly-advances-free-phase-depth
kind: claim
title: The diagonal support HNN exactly advances one free-phase layer
artifacts:
  - research/artifacts/signed-hecke-common-type-normalization-2026-08-20.md
distinct_from:
  free-phase-context-support-is-a-proper-free-factor: that identifies the one-layer support subgroup; this constructs the most natural asymmetric infinite-edge map from that subgroup into two commuting copies.
  symmetric-free-support-hnn-remains-hyperlinear: that identifies one support copy with another; this sends one copy diagonally into the product of both copies and really changes every off-diagonal coefficient.
---

Let `L_0,L_1` be commuting copies of the rank-`D-1` free group from `(FPS1)`,
with corresponding generators `a_i^(0),a_i^(1)`, and define the diagonal
embedding

```text
delta:L_0 -> L_0 times L_1,
delta(a_i^(0))=a_i^(0)a_i^(1).                           (DHA1)
```

It is injective because projection onto the first factor is a left inverse.
In the HNN extension

```text
E_delta=<L_0 times L_1,t |
 t a_i^(0)t^(-1)=a_i^(0)a_i^(1), 2<=i<=D>,              (DHA2)
```

let `t` commute with the finite root group `K`.  For root matrix units define

```text
Phi_0(E_(ij))=E_(ij)a_i^(0)(a_j^(0))^(-1),
Phi_01(E_(ij))
 =E_(ij)(a_i^(0)a_i^(1))(a_j^(0)a_j^(1))^(-1).          (DHA3)
```

Then

```text
t Phi_0(f)t^(-1)=Phi_01(f)                               (DHA4)
```

for every `f in M_D(C)`.  Thus an infinite associated subgroup can transport
the entire escaped context matrix block termwise and append a second phase
layer with a finite group presentation.  This is an exact asymmetric
infinite-edge transport, not merely equality of traces or ranks.

Nevertheless `(DHA2)` is residually finite and hence hyperlinear, so phase
depth advancement alone cannot be the decisive no-CE chord operation.
