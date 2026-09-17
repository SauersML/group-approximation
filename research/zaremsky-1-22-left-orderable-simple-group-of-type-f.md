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

- (z1-22-lo-simple-bm, 2026-09-13) **Lattices in products of trees.**
  `some-left-orderable-simple-group-has-type-f-via-burger-mozes` requires
  `some-simple-lattice-in-a-product-of-trees-is-left-orderable`. The expected truth for
  the explicit Burger–Mozes lattices is the opposite, through a Deroin–Hurtado type rigidity
  theorem (`irreducible-tree-product-lattices-are-not-left-orderable`, open). The transcription
  of that proof is recorded in `research/artifacts/zp-tree-lattice-left-orderability-2026-09-13.md`.
  Its circle-rigidity input is settled (`tree-product-lattice-circle-actions-have-fixed-points`).
- (z1-22-lo-simple-bm, 2026-09-13; corrected after z1-22-lo-simple-thompson) **Dimension levers
  on the line.**
  - A group of finite cohomological dimension has at most `cd G` nontrivial elements with
    pairwise disjoint supports (`finite-cd-line-groups-bound-disjointly-supported-families`), so a
    witness contains no `F'` and no `Z ≀ Z`.
  - In every faithful action of a finitely generated simple group, rigid stabilizers of proper
    subintervals are trivial (`fg-simple-line-groups-have-no-one-sided-supports`). So micro-support
    (`finite-cd-groups-have-no-micro-supported-line-action`) gives no information about simple
    candidates.
  - Peer lane z1-22-lo-simple-thompson works the Thompson-like family.
- (sw-102, 2026-09-17) **Explicit simple tree lattices killed by finite certificates.**
  Rattaggi's incoherent simple group `Λ` (in `Aut(T_12)×Aut(T_10)`) and his torsion-free simple
  `Σ_0` (in `Aut(T_12)×Aut(T_8)`) are not left-orderable
  (`rattaggi-simple-lattices-are-not-left-orderable`, ESTABLISHED, computer-certified). Each has
  an unsatisfiable sign-choice certificate on the radius-4 parity ball: 301 and 207 product
  relations, checked by relator rewriting and DPLL. These are two type-F simple witnesses killed
  without the open Deroin–Hurtado analogue.
  - Rattaggi's A6 `(6,6)`-kernel `Λ_0`, conjectured simple, is also not left-orderable (412
    triples at radius 6).
  - There is no certificate at radius 4 for Wise's `D_0`.
  - Next step: search larger balls there, or extract a local mechanism from the certificates for
    a class-wide obstruction.
