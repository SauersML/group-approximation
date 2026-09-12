---
rg: 2
id: support-return-charts-meet-in-two-pauli-pairs
kind: claim
title: The two support-return charts meet exactly in two Pauli pairs
artifacts:
  - experiments/support_partial_whitehead_native_return_audit.py
  - research/support-return-chart-intersection-proof.md
distinct_from:
  support-return-gives-gauged-native-loop: that constructs each odd native loop and proves its support Whitehead leaves the fixed Pauli chart; this compares the two transported charts exactly and tests their relative word.
  same-center-whitehead-gram-is-not-native-selector-gram: that compares the two native adjacent-swap unitaries on one fixed three-pair packet; this computes the intersection of the two nonnative support-return charts and the action of `W_1W_2` on it.
  recentered-order-seven-heads-have-actor-holonomy: that closes a five-pair actor algebra for the order-seven heads; this finds the largest common subpacket of the two prefix-support chart transports and proves that it loses one of the three selector bits.
---

**ESTABLISHED CHART-INTERSECTION FENCE.**  Let `E` be the
`128`-element same-center three-pair Pauli group and put

```text
E_1=W_1EW_1,          E_2=W_2EW_2,                    (SCI1)
```

with `W_1=W_79(e_0,e_0)` and `W_2=W_79(e_000,e_000)` as in the
support-return odd loops.  Exact Leavitt-matrix closure gives

```text
|E_1|=|E_2|=128,       E_1 != E_2,
E_1 intersect E_2
 =W_1<A_2,A_3,B_2,B_3>W_1
 =W_2<A_2,A_3,B_2,B_3>W_2,
|E_1 intersect E_2|=32.                               (SCI2)
```

Thus the two charts have a positive common two-pair Pauli packet, but not
the three-pair `M_8(C)` label required for a three-bit one-eighth control.

The two support projections are nested, so their relative word is exactly

```text
S=W_1W_2=W_79(e_0+e_000,e_0+e_000).                   (SCI3)
```

It does not normalize `E`.  In generator order
`(A_1,A_2,A_3,B_1,B_2,B_3)`, membership of the six conjugate images in
`E` is

```text
(0,1,1,0,1,1).                                        (SCI4)
```

On the other hand,

```text
SE_1S^(-1)=E_2,                                       (SCI5)
```

and `S` centralizes every element of the intersection in `(SCI2)`.  Hence
on the common two-qubit label its action is identity-label tensored with an
uncontrolled reservoir unitary.  The common packet therefore does not
authenticate the relative chart gauge.

Neither the two odd identities nor the native braid ties the chart gauges.
Indeed tensor the two chart transporters independently by signs
`epsilon_1,epsilon_2 in C_2`.  Each identity

```text
J_i=W_i Khat_i W_i                                    (SCI6)
```

contains its sign twice, so `J_i` and the braid
`J_1J_2J_1=J_2J_1J_2` are unchanged.  The relative word acquires the
arbitrary sign `epsilon_1epsilon_2`; assign the same sign to the named
occurrence `S` in `(SCI3)`.  This is an exact finite `C_2 times C_2`
chart-groupoid gauge model of all displayed rows.  Consequently no equation
between `w_1,w_2` or between `h_1,h_2` follows from SRL plus the braid.

The next useful relation must type `S` nontrivially on a packet retaining
all three Pauli pairs, or independently identify one of the two chart
transporter gauges.  Restriction to `(SCI2)` makes `S` label-trivial and
erases the bit needed for the one-eighth selector.

No Property T, Kazhdan input, trace hypothesis, literature theorem, local
computation, or Lean compilation is used.

DERIVATION
support-return-chart-intersection-proof
