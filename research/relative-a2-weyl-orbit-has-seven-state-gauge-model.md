---
rg: 2
id: relative-a2-weyl-orbit-has-seven-state-gauge-model
kind: claim
title: The full relative A2 Weyl orbit has an exact seven-state gauge model
artifacts:
  - research/relative-a2-weyl-seven-state-proof.md
distinct_from:
  mixed-cross-zero-squares-have-four-state-gauge-model: that uses an unconstrained involutory relative reservoir gauge; this imposes the actual order-three A2 relative Weyl word, its full braid action, and both nontrivial orbit cross-zero rows.
  adjacent-prefix-whitehead-braid-conjugates-reservoir-gauges: that computes how adjacent prefix Whiteheads conjugate abstract reservoir involutions; this gives an explicit finite carrier on which the complete native label braid and a nontrivial order-three reservoir holonomy coexist.
  cross-zero-breaks-reverse-whitehead-support-fusion: that excludes a common scalar coordinate support for the two transported branches; this cycles one non-scalar branch packet through two fresh target reservoirs before returning to its overlapping source support.
---

**ESTABLISHED FULL-RELATIVE-WORD COUNTERMODEL.**  Choose a fixed root-index
transport `U_0` with

```text
U_0 x_14(q) U_0^(-1)=x_12(q).
```

Let `H` be the native `A_2` Coxeter word, the product of the adjacent Weyl
swaps on indices `1,2,3`, so that

```text
H:x_12(q) -> x_23(q) -> x_31(q) -> x_12(q),
H^3=1.                                                   (RAW1)
```

Take `U_1=HU_0`.  The requested source relative word is therefore

```text
R=U_0^(-1)U_1=U_0^(-1)HU_0,
R^3=1.                                                   (RAW2)
```

Imposing the full Weyl/braid action means transporting the complete
positive/opposite branch-one packet around all three positions in `(RAW1)`.
Both nontrivial relative positions are composable with `x_12(q_0)`, and the
two coefficient rows `q_0q_1=q_1q_0=0` give both oriented cross-zero words.

These rows kill the four-state involutory gauge model, but not finite
holonomy.  On `H_0=C^7` put

```text
P_0=proj<e_1,e_2>,              P_1=proj<e_2,e_3>,
P_A=proj<e_1,e_3>,                                    (RAW3)
G=(e_2 e_4 e_5)(e_3 e_6 e_7).                         (RAW4)
```

Then `G^3=1` and

```text
GP_1G^*=proj<e_4,e_6>,
G^2P_1G^(-2)=proj<e_5,e_7>,                            (RAW5)
```

both orthogonal to `P_0`, whereas

```text
rank(P_0P_1)=1.                                       (RAW6)
```

Control the complete finite positive/opposite payload packet by these
projections as in `mixed-cross-zero-squares-have-four-state-gauge-model`.
Implement `R` as the native order-three label action tensored with `G` on
the reservoir.  Equations `(RAW4)--(RAW5)` make its order law, adjacent
Weyl braid, every packet occurrence square, and both orbit cross-zero rows
exact.  The source fold remains exact because `P_A` is the symmetric
difference of the equirank `P_0,P_1`, and its mark is nontrivial.

Thus the actual finite relative Weyl orbit does not supply the missing
gauge lock.  It only forces the moving branch to use two fresh reservoirs.
Any successful fixed mixed relation must compare one of those returned
reservoirs directly with the **source intersection** before the order-three
orbit closes; the Coxeter order and all root-position covariance rows by
themselves permit the seven-state escape.

This is a packet-level exact countermodel to the proposed relative-word
promotion, not a representation of the full signed Leavitt group.  No
Property `(T)`, Kazhdan input, stability theorem, trace hypothesis, or
literature result is used.

DERIVATION
relative-a2-weyl-seven-state-proof

