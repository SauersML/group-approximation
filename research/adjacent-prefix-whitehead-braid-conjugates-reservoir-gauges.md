---
rg: 2
id: adjacent-prefix-whitehead-braid-conjugates-reservoir-gauges
kind: claim
title: The adjacent prefix Whitehead braid conjugates the two reservoir gauges
artifacts:
  - research/adjacent-prefix-whitehead-braid-proof.md
distinct_from:
  two-mixed-pauli-commutators-lock-the-relative-reservoir-gauge: that starts from a positive cross-Gram polar corner and moves a relative unitary into the packet commutant; this obtains conjugacy of the two reservoir involutions from an exact Coxeter braid on a common carrier.
  binary-leavitt-native-two-scale-cross-gram-positive: that needs cross-Gram overlap for the two actual coefficient transports; this gives the stronger exact conjugacy of their reservoir factors after the common-carrier occurrence typing.
---

Use the common carrier, three Pauli pairs, and adjacent partial-Whitehead
words `W_1,W_2` of
`same-center-prefix-whiteheads-are-uncontrolled-adjacent-swaps`.  In the
elementary Leavitt group their standard partial-swap images satisfy

```text
W_1^2=W_2^2=1,
W_1W_2W_1=W_2W_1W_2.                                  (APB1)
```

On the common marked carrier, write

```text
W_1=SWAP_(1,2) tensor V_1,
W_2=SWAP_(2,3) tensor V_2.                             (APB2)
```

Then `V_1,V_2` are involutions and

```text
V_1V_2V_1=V_2V_1V_2.                                  (APB3)
```

In particular they are unitarily conjugate:

```text
V_2=(V_1V_2)V_1(V_1V_2)^(-1).                         (APB4)
```

Thus the literal Leavitt prefix chain contains an exact, entirely
Property-T-free same-gauge mechanism for these two adjacent one-quarter
transport labels.  It does **not** prove that the separate controlled
selector reflections with label fractions `1/4` and `1/8` inherit those
reservoir factors.  That attachment is the occurrence-typing gap isolated by
`same-center-whitehead-gram-is-not-native-selector-gram`.

DERIVATION
adjacent-prefix-whitehead-braid-proof
