---
rg: 2
id: mixed-cross-zero-squares-have-four-state-gauge-model
kind: claim
title: The mixed cross-zero squares have an exact four-state reservoir-gauge model
artifacts:
  - research/mixed-cross-zero-four-state-gauge-proof.md
distinct_from:
  cross-zero-breaks-reverse-whitehead-support-fusion: that rules out scalar packet transports which preserve one common coordinate reservoir; this uses different reservoir gauges for the two native transports and makes their target supports disjoint while their source supports overlap.
  one-arm-range-sum-whitehead-has-marked-model: that moves complementary controlled Pauli arms through a three-character sector; this carries the complete positive/opposite reverse-product packet and satisfies the new composable cross-zero mixed squares exactly.
  literal-whiteheads-give-gauged-moving-bridge-table: that identifies an abstract multiplicity gauge on moving Whitehead bridges; this gives the smallest explicit finite projection geometry realizing precisely the gauge needed to defeat the proposed cross-Gram promotion.
---

**ESTABLISHED EXACT NON-SCALAR HOLONOMY FENCE.**  The finite-matrix lemma
suggested after `cross-zero-breaks-reverse-whitehead-support-fusion` is
false.  On `H_0=C^4` with basis `e_1,...,e_4`, put

```text
P_0=proj<e_1,e_2>,              P_1=proj<e_2,e_3>,
P_A=P_0 symmetric_difference P_1=proj<e_1,e_3>.       (MCZ1)
```

Thus the three commuting source projections have equal rank two, the fold
is exact, and

```text
rank(P_0P_1)=1.                                       (MCZ2)
```

Let `U_0=1` and let `U_1` swap `e_2,e_4`.  Then

```text
Q_0=U_0P_0U_0^*=proj<e_1,e_2>,
Q_1=U_1P_1U_1^*=proj<e_3,e_4>,
Q_0Q_1=0.                                             (MCZ3)
```

Take the finite positive/opposite payload packet `K` from
`reverse-product-whitehead-fold-has-finite-fusion` in any faithful finite
unitary representation.  For `g in K` and a projection `P`, write

```text
g[P]=(1-P) tensor 1 + P tensor g.                     (MCZ4)
```

Put the complete child-zero packet under `P_0`, the complete child-one
packet under `P_1`, and the parent packet under `P_A`.  Since the base
Whitehead `w` is an involution, the shared reverse-product relation is exact:

```text
w[P_0]w[P_1]=w[P_A].                                  (MCZ5)
```

Conjugate **every** positive and opposite occurrence of branch `i` by
`U_i tensor 1`.  This satisfies both mixed Weyl squares literally, not only
their central output signs.  The transported composable roots are supported
under `Q_0,Q_1`; hence their commutator is one by `(MCZ3)`, even though the
two scalar base roots do not commute.

Native parent-to-child Whitehead transports also exist exactly because
`P_A,P_0,P_1` have equal rank.  Choose carrier unitaries sending `P_A` to
`P_i` and attach the fixed label action of the native word on the payload
factor.  All source fold, reverse-product opposite-root, packet transport,
mixed-square, and crossed-zero rows are therefore exact, while the parent
packet is nontrivial.

This disproves any dimension-independent estimate of the form

```text
||P_0P_1|| <= C max(prototype defects + ||Q_0Q_1||),   (MCZ6)
```

as well as every rank/integrality variant with a positive lower charge from
the source intersection: the right side is zero in this exact model, while
`P_0P_1` has rank one and norm one.  Coordinate-dependent spectral cuts do
not help because all projections here are already exact spectral
projections with eigenvalues zero and one.

The missing relation is now a **relative reservoir-gauge lock**.  It must
couple `U_0^*U_1` to the source packet strongly enough that disjoint target
supports force disjoint source supports.  Adding more separate mixed squares
for the two branches will not do this: the construction conjugates each
complete packet, including all opposite factors, by its own gauge.

This is a packet-level exact countermodel to the proposed quantitative
lemma, not a representation of the full signed Leavitt group.  No Property
`(T)`, Kazhdan input, stability theorem, trace hypothesis, or literature
result is used.

DERIVATION
mixed-cross-zero-four-state-gauge-proof

