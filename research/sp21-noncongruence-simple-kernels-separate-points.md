---
rg: 2
id: sp21-noncongruence-simple-kernels-separate-points
kind: claim
title: Each nontrivial element of some cocompact arithmetic Sp(2,1) lattice lies in only finitely many alternating or large-rank simple quotient kernels
distinct_from:
  sp21-lattice-few-alternating-and-large-rank-quotients: that asks for finitely many such kernels in total; this asks only that each nontrivial element lie in finitely many of them, is implied by that claim, and still yields a hyperbolic group without finite quotients
  sp21-lattice-has-congruence-subgroup-property: that asks for a finite congruence kernel, which controls every finite quotient; this constrains only the alternating and large-rank simple quotients, and only through intersections of their kernels
  normal-subgroups-of-arithmetic-lattices-are-congruence-open: that is the established arithmetic fact for congruence quotients, whose kernels meet any nontrivial normal subgroup in only finitely many ways; this is the open analogue for the complementary, non-congruence simple quotients
---

Let `Γ` be a torsion-free cocompact arithmetic lattice in `Sp(2,1)`, set up as in
`sp21-bounded-rank-simple-quotients-almost-all-congruence`. Assert that for some
`r >= 1` the following holds. Every `g ∈ Γ \ {1}` lies in only finitely many
normal subgroups `N ⊴ Γ` for which `Γ/N` is an alternating group, or a finite
simple group of Lie type of Lie rank `> r`.

**Equivalent forms.** Since `Γ` is torsion-free, each of the following is
equivalent to the assertion.
- Every infinite family of such kernels intersects trivially.
- For every `1 != M ⊴ Γ`, the quotient `Γ/M` has only finitely many simple
  quotients of these types.
- Along every infinite sequence `χ_j` of such simple quotients, and for every
  `g != 1`, the order of `χ_j(g)` tends to infinity. Here `g^n != 1` for every
  `n`.

**Relations.**
- It follows from `sp21-lattice-few-alternating-and-large-rank-quotients`, where
  there are only finitely many kernels in total.
- It is the non-congruence analogue of the lemma in Lubotzky, arXiv:1105.4785,
  §4, Remark 4.1: for an arithmetic group, "the intersection of any infinite
  collection of normal congruence subgroups must be finite and central".

**Payoff.** Route `quotientless-hyperbolic-via-sp21-noncongruence-separation`
turns the assertion into an infinite hyperbolic group without finite quotients.
Contrapositive: if every hyperbolic group is residually finite, then for every
such `Γ` and every `r`:
- some nontrivial element lies in infinitely many alternating or rank-`> r`
  simple quotient kernels;
- more strongly, the route's steps 2–3 show that every proper, torsion-free,
  non-elementary hyperbolic quotient `Γ/M` has infinitely many simple quotients
  of these types.

## Attempts

- **From the finiteness form.** `sp21-lattice-few-alternating-and-large-rank-quotients`
  implies this claim. No route is recorded, because that claim already feeds the
  same target directly.
- **(T) and hyperbolicity alone.** They do not bound alternating quotients
  (`caprace-kassabov-hyperbolic-kazhdan-alternating-quotients`). The known
  examples have torsion, so separation for torsion-free groups is not decided by
  them.
- **Random relators.** `random-relators-kill-small-simple-quotients-of-kazhdan-groups`
  kills every alternating quotient of order at most `λ^(-L)` that contains `k`
  random relators of length `L`. The alternating quotients that survive a random
  quotient are large, and their kernels contain every relator. So they are a
  failure of this claim at the relators, and counting at one relator length
  cannot reach them.
- **Superrigidity is blind here.** An ultraproduct of alternating quotients, or of
  quotients of unbounded rank, is a Hamming or rank-metric approximation, not a
  linear representation. So the Łoś argument of
  `sp21-bounded-rank-simple-quotients-almost-all-congruence` has no purchase on it.
