---
rg: 2
id: barlak-li-uct-iff-z2-z3-actions-fix-cartan
kind: claim
title: The UCT problem is equivalent to outer strongly approximately inner Z_2- and Z_3-actions on O_2 fixing a Cartan subalgebra
distinct_from:
  barlak-li-two-half-iff-z2-actions-fix-cartan: that is the earlier equivalence for algebras KK-equivalent to their M_(2^∞)-stabilization only; this is the full Problem II, using both primes 2 and 3.
  stw99-problem-ii-nuclear-uct: that is the open problem; this is a proved equivalence with a dynamical statement about O_2 alone.
artifacts:
  - research/artifacts/stw-uct-reduction-map-2026-09-11.md
---

**ESTABLISHED (literature).**  Barlak--Li, *Cartan subalgebras and the UCT
problem, II*, arXiv:1704.04939v2, Theorem 1.4: the following are equivalent.

1. Every separable nuclear C\*-algebra satisfies the UCT.
2. For every prime `p ≥ 2` and every outer strongly approximately inner action
   `α : Z_p ↷ O_2` there is an inverse semigroup `S ⊂ O_2` of partial isometries
   inducing `O_2 ≅ C*_tight(S)` such that `S` is `α`-homogeneous, `C*(E)` is a
   Cartan subalgebra with Cantor spectrum in both `O_2^α` and `O_2`, and unitaries
   in `O_2^α` witnessing approximate representability can be chosen in `C*(E)`.
3. Every outer strongly approximately inner `Z_p`-action on `O_2` with `p = 2` or
   `p = 3` fixes some Cartan subalgebra `B ⊆ O_2` globally.

The engine is their Theorem 1.2: for an outer approximately representable
`α : Z_n ↷ A` on a unital UCT Kirchberg algebra with `A ⋊_α Z_n` absorbing
`M_(n^∞)`, the crossed product satisfies the UCT iff some Cartan subalgebra
`C ⊂ A` has `α(C) = C`.  Their Corollary 4.15 applies it to `O_2` with cyclic
groups of prime power order.
