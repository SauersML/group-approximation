---
rg: 2
id: barlak-li-two-half-iff-z2-actions-fix-cartan
kind: claim
title: The UCT for M_(2^∞)-stable nuclear algebras is equivalent to outer strongly approximately inner Z_2-actions on O_2 fixing a Cartan subalgebra
distinct_from:
  barlak-li-cartan-subalgebras-force-uct: that collects the positive Cartan theorems; this is the separate equivalence for the half of Problem II localized at 2.
  uct-for-two-infinity-absorbing-nuclear-algebras: that is the open half itself; this is the proved equivalence converting it into a question about order-two automorphisms of O_2.
artifacts:
  - research/artifacts/stw-uct-reduction-map-2026-09-11.md
---

**ESTABLISHED (literature).**  Barlak--Li, Adv. Math. 316 (2017)
(arXiv:1511.02697v3), Theorem 1.8: the following are equivalent.

1. Every separable nuclear C\*-algebra `A` that is KK-equivalent to
   `A ⊗ M_{2^∞}` satisfies the UCT.
2. For every unital `M_{2^∞}`-absorbing Kirchberg algebra `A` in Cuntz standard
   form there are a strongly approximately inner action `β : Z_2 ↷ O_2` and a
   Cartan subalgebra `B ⊆ O_2` with `O_2 ⋊_β Z_2 ≅ A` and `β` fixing `B`
   pointwise.
3. Every outer strongly approximately inner `Z_2`-action on `O_2` fixes some
   Cartan subalgebra `B ⊆ O_2` pointwise.
4. Every outer strongly approximately inner `Z_2`-action on `O_2` fixes some
   Cartan subalgebra `B ⊆ O_2` globally.

The proof combines their Proposition 1.6 and Theorem 1.7 with Izumi's
classification of outer strongly approximately inner `Z_2`-actions on `O_2`
(Izumi, Theorem 4.8).  Statement 1 is exactly
`uct-for-two-infinity-absorbing-nuclear-algebras`: `A ⊗ M_{2^∞}` is
KK-equivalent to its own `M_{2^∞}`-stabilization, and conversely a KK-equivalence
`A ≃ A ⊗ M_{2^∞}` transports the UCT.
