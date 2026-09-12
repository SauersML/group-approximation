---
rg: 2
id: inner-pauli-occurrence-labels-are-tietze-removable
kind: claim
title: Noncentral inner-Pauli occurrence labels are Tietze-removable
distinct_from:
  fixed-extraspecial-packet-is-morita-neutral-for-code-rounding: that treats packet-central logical variables representation-theoretically; this removes even maximally pinned noncentral inner labels at the abstract presentation level.
  fixed-k-code-product-gap-is-a-twisted-intertwiner-test: that tests a chosen direct-product generating set; this shows the proposed Pauli-label construction is merely such a generating-set twist.
---

# Noncentral inner-Pauli occurrence labels are Tietze-removable

ESTABLISHED. Let `K` be any fixed group and let a homogeneous face system
present `Gamma_H=<y_i | F>`. Choose involutions `k_i in K` which satisfy the
same commuting product-one relation on every face. Adjoin a copy of `K` and
logical involutions `r_i`, and impose the strongest natural noncentral label
pinning:

```text
r_i h r_i^{-1} = k_i h k_i^{-1}       for every h in K.   (IP1)
```

Together with the original homogeneous face relations on the `r_i`, the
resulting universal group is exactly

```text
K x Gamma_H.                                             (IP2)
```

Indeed set `y_i=k_i^{-1}r_i=k_i r_i`. Relation `(IP1)` says precisely that
`y_i` centralizes `K`. Because `r_i` and `k_i` are involutions, so is `y_i`.
On a face, the `k_i` commute and have product one. Therefore

```text
[r_i,r_j]=1  iff [y_i,y_j]=1,
product_(i in face) r_i=1  iff product_(i in face) y_i=1.
```

This change of generators and its inverse are Tietze transformations, proving
`(IP2)`.

For the order-32 Magic-Square packet, every chosen noncentral Pauli direction
acts on the packet by such an inner automorphism. Hence labeling each
low-rate code occurrence by Pauli directions does not couple the code to the
packet: it only replaces the direct-product generators `(1,y_i)` by the
skewed generators `(k_i,y_i)`.

In the `J=-1` representation, this is visible as

```text
r_i = P(k_i) tensor Q_i.
```

Every exact contextual family `{Q_i}` for `Gamma_H` lifts, with identical
normalized HS face and commutator energies. Thus even maximal finite-packet
conjugation pinning leaves the full multiplicity escape. Imposing fewer
packet-action relations cannot exclude this tensor model.

The only finite-packet variant not covered by this no-go must use genuinely
outer/projective transport or relations which mix several occurrence
variables with packet words not themselves forming a K-valued local solution.
For fixed `K`, such a route must explicitly defeat the residual finite
cocycle-twisted multiplicity algebra; noncentral labels alone do not do so.

