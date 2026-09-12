---
rg: 2
id: o2-zp-cartan-fixing-iff-rokhlin-uct-ascent
kind: claim
title: Cartan-fixing for order-p actions on O_2 is equivalent to the UCT ascending along Rokhlin Z_p-actions whose crossed product is O_2
distinct_from:
  o2-zp-cartan-fixing-all-primes-or-at-most-one: that glues the prime halves together and bounds the set of primes where Cartan-fixing holds; this rewrites one prime half as an ascent statement about Rokhlin actions on Kirchberg algebras.
  barlak-li-p-half-iff-zp-actions-fix-cartan: that is the literature equivalence between the UCT for M_(p^∞)-stable algebras and Cartan-fixing; this is a derived equivalence between Cartan-fixing and UCT ascent along Rokhlin actions, obtained by passing to the dual action.
  bootstrap-class-zp-actions-on-o2-fix-a-cartan: that proves Cartan-fixing for the actions in the equivariant bootstrap class; this proves no case, and restates the whole prime half on the dual side.
artifacts:
  - research/artifacts/uct-o2-cyclic-actions-2026-09-12.md
---

**ESTABLISHED (derivation, this repository).**  Let `p` be a prime.

- `D_p`: every outer, strongly approximately inner action `α : Z_p ↷ O_2`
  fixes some Cartan subalgebra of `O_2` globally.
- `Asc_p`: every unital Kirchberg algebra `B` that carries a Rokhlin action
  `δ : Z_p ↷ B` with `B ⋊_δ Z_p ≅ O_2` satisfies the UCT.

Then `D_p ⟺ Asc_p`.

Proof: `o2-zp-cartan-fixing-iff-rokhlin-uct-ascent-proof`.

**What this says.**  A counterexample to the UCT at the prime `p` is exactly a
non-UCT unital Kirchberg algebra carrying a Rokhlin `Z_p`-action with crossed
product `O_2`. By `o2-zp-cartan-fixing-all-primes-or-at-most-one`, Problem II is
`Asc_p ∧ Asc_q` for any two distinct primes. The UCT always passes *down* from
`B` to `B ⋊_δ Z_p`, since that crossed product is `O_2`, so the prime half is
precisely the question of whether it passes *up*.

**Credit.**  This is a restatement through the dual action. It uses only
Barlak--Li II Corollary 4.15, the duality in their Theorem 2.8, and Takai
duality. It is close in spirit to Barlak--Szabó, Trans. Amer. Math. Soc. 369
(2017), Theorem 4.17, and no priority is claimed.
