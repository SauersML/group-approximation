---
rg: 2
id: jones-subgroup-coamenable-iff-thompson-f-amenable
kind: claim
title: Jones' subgroup is co-amenable in Thompson's group F if and only if F is amenable
distinct_from:
  jones-subgroup-is-co-amenable-in-thompson-f: that is the open co-amenability statement; this proves it equivalent to amenability of F.
  jones-subgroup-coamenable-iff-dyadic-extensive-amenability: that is the equivalence with extensive amenability of the dyadic action; this pushes one step further to amenability of F itself.
  thompson-f-is-amenable: that is amenability of F; this is an equivalence reducing a question of Aiello–Brothier–Conti to it.
---

**ESTABLISHED.** `\vec F` is co-amenable in `F` if and only if `F` is amenable.

**Consequences.**
- The question of Aiello–Brothier–Conti (arXiv:1901.10597, Remark 4.7), whether `1_F ≺ λ_(F/\vec F)`, is
  equivalent to Zaremsky Question 2.1 (`zaremsky-2-01-thompson-f-amenable`).
- A proof of nonamenability through a spectral gap for `λ_(F/\vec F)` loses nothing relative to `λ_F`.
- Conversely, any certificate of co-amenability of `\vec F` (e.g. from the Jones chromatic representation at
  `Q = 2` weakly containing the trivial representation) proves amenability of `F`.

**Mechanism.**
1. Co-amenability forces extensive amenability of `F ↷ D`, through the slope-parity point character of the
   digit-parity boundary cocycle (`dyadic-extensive-amenability-if-jones-subgroup-coamenable`).
2. Extensive amenability of `F ↷ D` forces amenability of `F`, by Juschenko–Matte Bon–Monod–de la Salle
   Corollary 1.4 applied to the graph of the breakpoint cocycle `F → ℤ^(D)`, which has trivial kernel.
   Step 2 was also posted independently on the swarm bus by swarm-0917-w4-f-decomp on 2026-09-17.

Proof route: `jones-coamenable-iff-f-amenable-breakpoint-cocycle-proof`.
