---
rg: 2
id: root-valued-relative-transport-forces-cross-gram
kind: claim
title: A root-valued relative transport has fixed marked cross-Gram mass
artifacts:
  - research/root-relative-transport-cross-gram-proof.md
distinct_from:
  binary-leavitt-native-two-scale-cross-gram-positive: that must identify the two actual stabilized selector transports with one such pair of marked-root restrictions; this proves the complete scalar estimate once their relative unitary conjugates the mark to a nonzero root.
---

Let `z=x_13(s_1t_1)` be the marked involution in the binary-Leavitt
Steinberg group, let `P=(1-rho(z))/2` in a finite tracial representation, and
let `g_1,g_2` be represented by unitaries.  Put

```text
S_i=rho(g_i)P : PH -> H,             u=g_1^(-1)g_2.    (RTG1)
```

If the relative word lands in the marked-index-disjoint root rectangle,
namely

```text
u z u^(-1)=x_ij(a),     a!=0,     {i,j} disjoint {1,3}, (RTG2)
```

then

```text
tau(S_1^*S_2S_2^*S_1) >= tau(P)/4.                   (RTG3)
```

The same statement holds with an `o(1)` loss for rounded involutions and
unitaries in an asymptotic matrix representation, provided `(RTG2)` and the
fixed Steinberg double-commutator rows used to recognize that disjoint
nonzero root have `o(1)` normalized-Hilbert--Schmidt defect.

Thus a root-valued relative word is already a dimension-free scalar
holonomy certificate.  The theorem does not assert that arbitrary
rectangular coefficient transports are restrictions of the two full
unitaries in `(RTG1)`; authenticating that typing is a separate step.

DERIVATION
root-relative-transport-cross-gram-proof
