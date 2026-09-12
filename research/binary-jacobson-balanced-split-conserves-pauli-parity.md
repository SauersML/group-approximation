---
rg: 2
id: binary-jacobson-balanced-split-conserves-pauli-parity
kind: claim
title: The balanced Jacobson two-branch split conserves Pauli parity
artifacts:
  - research/binary-jacobson-balanced-split-pauli-parity-proof.md
distinct_from:
  binary-jacobson-balanced-shift-transport-is-xor: that follows one raw root through the triangular balanced shift and obtains a symmetric-difference rank row; this follows a complete A2 source pair through the involutive split and computes the two branch-center signs.
  binary-jacobson-head-sector-has-native-two-qubit-packet: that supplies two independent negative-center branches on the head sector; this proves that the most literal balanced return cannot simultaneously see those two branches from one negative-center source factor.
  binary-jacobson-proper-active-cycle-is-amenable: that gives a marked MF fence for every proper directed subcycle; this identifies the exact parity conservation inside the two-edge occurrence and explains why the third, closing incidence is indispensable.
  opnorm-common-intertwiner-pi-gap-is-sparse-terminal: that gives the contradiction from a source M2 factor and a transverse target M4 tuple; this proves the balanced split never presents those two PI degrees on the same joint spectral cut.
---

**ESTABLISHED.**  Put

```text
J=F_2<S,T | TS=1>,       Q=1-ST,       P=ST,
```

and on coordinate rows `(2,4)` put

```text
h=[[Q,S],[T,0]],          h^2=1.                         (JBSP1)
```

Extend `h` by the identity on the other rows of `EL_5(J)`.  For the
constant A2 source pair

```text
U=x_12(1),                V=x_23(1),
```

conjugation by this one literal balanced occurrence gives

```text
h U h = A B,              A=x_12(Q),   B=x_14(S),
h V h = C D,              C=x_23(Q),   D=x_43(T).       (JBSP2)
```

The two branch pairs cross-commute and have centers

```text
[A,C]=w_Q=x_13(Q),        [B,D]=w_P=x_13(P),
w_Q w_P=x_13(1)=[U,V].                                  (JBSP3)
```

Let a unitary representation be restricted to any nonzero joint spectral
cut on which `w_Q,w_P` have signs `epsilon_Q,epsilon_P in {+1,-1}`.  Then:

* the source pair `(U,V)` is a Pauli/M2 pair exactly when
  `epsilon_Q epsilon_P=-1`;
* the first target branch `(A,C)` is Pauli exactly when `epsilon_Q=-1`;
* the second target branch `(B,D)` is Pauli exactly when `epsilon_P=-1`.

Therefore a source `M_2` sector contains exactly one negative target branch.
On the sector where both target branches are Pauli and generate the
transverse `M_4` packet, the source commutator is `+1`, so the source words
commute.  There is no joint cut on which this balanced split supplies both
the degree-two source factor and the degree-four target tuple required by
the common-intertwiner PI endpoint.

This is an occurrence statement, not a dimension estimate: arbitrary
spectator amplification leaves the sign table unchanged.  Hence the
balanced involution and the two forward constant roots cannot be the missing
PI bridge.  Any successful use of the minimal directed-cycle package must
consume the third, closing root in a genuinely non-conjugacy overlap; merely
using it to form another constant Weyl transport remains inside the finite
constant/`Q` envelope.

DERIVATION
binary-jacobson-balanced-split-pauli-parity-proof
