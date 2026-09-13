---
rg: 2
id: zaremsky-1-22-left-orderable-simple-group-of-type-f
kind: claim
title: "Zaremsky Problem 1.22 resolved: is there a left-orderable simple group of type F?"
root: true
distinct_from:
  infinite-left-orderable-kazhdan-group: that asks for a left-orderable group with property (T); this asks for a left-orderable simple group with a finite classifying space, and neither property implies the other
  finitely-generated-simple-groups-are-not-biorderable: that rules out bi-invariant orders on finitely generated simple groups; this asks for a left-invariant order on a simple group of type F, where no such obstruction is known
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 1, Problem 22, verbatim:

> 22. (Added 10/2/25) Find an example of a left-orderable simple group of type F.
> (Type F∞ was done by Hyde–Lodha. If Burger–Mozes groups are left-orderable then
> they'd do it.)

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-1-22-by-yes` requires `some-left-orderable-simple-group-has-type-f`.
- **No**: `zaremsky-1-22-by-no` requires `no-left-orderable-simple-group-has-type-f`.

Never write a `requires: []` route into this claim.

**Precise reading.**

- `G` is *left-orderable* if it has a total order invariant under left
  multiplication. For countable `G` this is equivalent to a faithful action on `R` by
  orientation-preserving homeomorphisms.
- `G` is *simple* if `G ≠ 1` and its only normal subgroups are `1` and `G`.
- `G` is *of type F* if some finite CW complex is a `K(G,1)`.

An answer is one group with all three properties. A nontrivial left-orderable group is
torsion-free and infinite. A group of type F is finitely presented and has finite
cohomological dimension. So a witness is a finitely presented, torsion-free, infinite
simple group of finite cohomological dimension with a faithful action on the line.
The "Find" wording is answered by an explicit example; a proof that no such group
exists answers the question the other way.

**Known (read 2026-09-13).**

- Hyde–Lodha, arXiv:2302.04805 (v3, HTML render), Theorem 1.1: "There exist finitely
  presented (and type F∞) simple groups of orientation-preserving homeomorphisms of R."
  Their groups `Q_n = [Γ_n, Γ_n]` "have infinite geometric dimension" (their
  Proposition 1.4), so they are not of type F.
- A torsion-free simple cocompact lattice in `Aut(T_1) × Aut(T_2)` acts freely and
  cocompactly on the contractible square complex `T_1 × T_2`, so it is of type F.
  Burger–Mozes built such lattices (`burger-mozes-infinitely-transitive-tree-groups`,
  item 5). Hyde–Lodha write of the Burger–Mozes family: "For each of them it remains
  unknown whether it admits a nontrivial action by homeomorphisms on the real line."

## Attempts

- (z1-22-lo-simple-bm, 2026-09-13) Lattices in products of trees:
  `some-left-orderable-simple-group-has-type-f-via-burger-mozes` requires
  `some-simple-lattice-in-a-product-of-trees-is-left-orderable`. The expected truth for
  the explicit Burger–Mozes lattices is the opposite, through a Deroin–Hurtado type
  rigidity theorem (`irreducible-tree-product-lattices-are-not-left-orderable`, open).
- (z1-22-lo-simple-bm, 2026-09-13) Groups of finite cohomological dimension have no
  micro-supported action on the line (`finite-cd-groups-have-no-micro-supported-line-action`).
  So no group whose faithful actions on `R` are all micro-supported can be a witness;
  in particular a witness cannot come from the natural action of a micro-supported
  Thompson-like group. Peer lane z1-22-lo-simple-thompson works that family.
