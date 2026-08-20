---
rg: 2
id: support-packet-literal-tensor-covariance-is-blind
kind: claim
title: Literal tensor covariance cannot distinguish the support packet's forbidden simple
artifacts:
  - experiments/schur_packet_covariance_annihilator.py
distinct_from:
  support-packet-covariant-wedderburn-detector: that detects the forbidden sector by the shape of two commutant algebras; this proves the stronger-looking attempt to identify the two tensor representations themselves is necessarily blind.
  full-center-hnn-transport-cancels-schur-multiplicity: that treats full-center Pauli edge restrictions and Hilbert-dimension flow; this is a representation-ring annihilator theorem for arbitrary finite tensor coefficients.
---

Let `B_sub` be the order-128 support packet, let `A` be the set of all packet
simples in the three allowed `J=-1` central sectors `100,110,111`, and let
`T_101` be the unique forbidden simple.  For arbitrary finite-dimensional
packet representations `V_+` and `V_-`, if

```text
S tensor V_+ isomorphic to S tensor V_-       for every S in A,          (LTC1)
```

then

```text
T_101 tensor V_+ isomorphic to T_101 tensor V_-.                         (LTC2)
```

The conclusion also holds for virtual representations.  Consequently no HNN
cell that merely conjugates two literal diagonal packet representations can
be allowed-flat and forbidden-sensitive.  The surviving covariant detector
must compare a functor such as the commutant/Reynolds range, not the tensor
representations themselves.

The exact character audit gives additional coordinates for this obstruction.
The simultaneous tensor-annihilator of the twelve allowed simples has rank
`12` in the 38-dimensional complexified representation ring.  Adding tensor
multiplication by the forbidden simple does not shrink it.  On the 128 packet
elements the support incidences `(some allowed character is nonzero, the
forbidden character is nonzero)` are

```text
(false,false): 64,       (true,false): 56,       (true,true): 8.          (LTC3)
```

In particular `(false,true)` never occurs.
