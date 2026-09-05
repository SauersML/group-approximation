---
rg: 2
id: stw99-l-pi1-aut-splits-into-two-hom-groups
kind: claim
title: The fundamental group of Aut of a free-K-theory UCT Kirchberg algebra is the sum of two Hom groups
artifacts:
  - research/artifacts/stw99-l-six-kirchberg-loops-2026-09-05.md
---

Let `D` be a unital UCT Kirchberg algebra whose K-groups are finitely
generated and free and whose unit class `e_D = [1_D]` is primitive in
`K_0(D)`.  Then the reduced-KK invariant `Delta` of a based point-norm
continuous automorphism loop is an isomorphism of abelian groups

```text
Delta : pi_1(Aut(D), id)  ->  Hom(K_1(D), K_0(D)) (+) Hom(K_0(D)/Z e_D, K_1(D)).
```

Both summands are parity-reversing, as they must be: `Delta_alpha` lives
in `KK^1(D,D)`, and concretely, applying an automorphism loop to a
unitary produces a loop of unitaries, i.e. a `K_1 -> K_0` map.

Two consequences used downstream.  With the Bott convention in which the
loop `1 + (z-1)p` has class `[p]`, the `K_1 -> K_0` component of `Delta`
sends `[w]` to the Bott class of `z |-> alpha_z(w) w^*`; and a projection
fixed throughout the loop has zero reduced class, so a loop fixing a
generating set of `K_0(D)` has vanishing second component.  `Delta` is
natural for conjugation by a fixed isomorphism.
