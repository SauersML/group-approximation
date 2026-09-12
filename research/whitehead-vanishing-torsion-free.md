---
rg: 2
id: whitehead-vanishing-torsion-free
kind: claim
title: Whitehead group vanishing for torsion-free groups
root: true
distinct_from:
  whitehead-vanishing-universal-test-group: that claim is the same assertion concentrated on one explicitly constructed group, and is equivalent to this one; this is the global statement, and the equivalence is the content of the route between them rather than a duplication.
  whitehead-vanishing-recursively-presented-torsion-free: that claim restricts to finitely generated recursively presented groups, a countable class; this is the global statement over all torsion-free groups, and the reduction between them is a theorem, not a rephrasing.
  whitehead-vanishing-finitely-presented-torsion-free: that claim restricts to finitely presented groups; the established Whitehead-injective Higman embedding and finite-support reduction now prove it equivalent to this global statement.
  degree-one-assembly-surjective-torsion-free: that claim is about a map of spectra-level invariants being onto; this is the vanishing of a quotient group. They are equivalent by whitehead-is-degree-one-assembly-cokernel, which is the point of that node.
  hnn-torsion-theorem: that claim is combinatorial group theory -- torsion-freeness passes from the base of an HNN extension to the extension -- and produces torsion-free groups; this claim consumes torsion-freeness as a hypothesis and asserts something about K_1 of the integral group ring. Shared vocabulary, disjoint content.
  infinite-order-central-mark-group: that claim asks for a torsion-free finitely presented group carrying specific transport data for the non-MF program; this asserts a K-theoretic vanishing for every torsion-free group and requires no witness group at all.
  elementary-group-property-t-over-free-algebras: that is property (T) for a specific family of elementary matrix groups over free algebras, a representation-theoretic rigidity statement; this is vanishing of a Whitehead quotient for all torsion-free groups. Both mention matrix groups over rings and share nothing else.
  fournier-facio-torsion-free-skeleton: that describes the internal structure of one specific torsion-free non-sofic group; this is a universally quantified K-theoretic vanishing, and that group is not known to satisfy or violate it.
  torsion-free-countable-non-mf: that asks for one torsion-free countable group failing an operator-algebraic approximation property; this asserts an algebraic K-theory vanishing for every torsion-free group. Neither implies nor bears on the other, which is itself one of this node's recorded findings.
artifacts:
  - research/artifacts/whitehead-vanishing-audit-2026-08-17.md
  - research/artifacts/high-impact-literature-roots-audit-2026-08-31.md
---

If `G` is torsion-free then `Wh(G) = 0`, where

    Wh(G)  =  K_1(ZG) / < [+-g] : g in G >.

Conjecture 3.6 of Lueck's *Survey on the Farrell--Jones Conjecture*
(arXiv:2507.11337), stated there as "Let G be a torsionfree group. Then
Wh(G) vanishes", and open.  Known for the Farrell--Jones class: hyperbolic
groups, finite-dimensional CAT(0)-groups, lattices, 3-manifold groups,
S-arithmetic groups.

## Why it is a root of *this* graph

It is not this program's goal and it is not implied by anything here.  It is
a root because a resolution attempt was run against this repository's
material -- the Leavitt `K_1` development, the universal torsion-free coded
product, and the matrix-corona `K`-theory -- and the honest outcome of that
attempt is a set of reductions and obstructions worth keeping.  Three of the
audit's conclusions are permanently useful to this graph independently of
Whitehead: `augmentation-blocks-unital-leavitt-family`,
`topological-k1-cannot-detect-integral-whitehead`, and the corrected
`matrix-corona-product-k0-is-rank-bounded-sequences`.

Nonsoficity and non-MF-ness are **not** evidence either way.  They are
matrix-approximation properties; this is a quotient computation in algebraic
`K`-theory over `Z`.  No implication in either direction is proved in this
corpus or in the literature, and the operator-algebraic routes here supply a
zero-valued target rather than a detector.

## What a certificate must contain

*Proof.*  For every torsion-free `G`, every `A` in `GL_n(ZG)` admits, after
adding identity blocks, `A (+) I_r = E_1 ... E_m diag(+-g, 1, ..., 1)` with
each `E_i` elementary.  Equivalently, by
`whitehead-is-degree-one-assembly-cokernel`, surjectivity of the degree-one
assembly map.

*Disproof.*  A rigorously torsion-free `G`; a matrix `A` in `GL_n(ZG)` with
an exact inverse; an invariant `tau` on `K_1(ZG)` with `tau(E) = 0` on
elementary matrices and `tau([+-g]) = 0` for every `g`; and `tau([A]) != 0`.
A disproof is the negation of this claim, so per the kernel's semantics it
would be its own claim -- killing every route into this one leaves it open,
not refuted.

## Attempts

Four were run against this repository's material on 2026-08-17 and all four
died at an identified step; the audit artifact traces each to the line where
it stops.

1. **Import the Leavitt `K_1`-swindle.**  This repository proves
   `K_1(L_k(1,2)) = 0` over every field.  *Dies* at the augmentation:
   `augmentation-blocks-unital-leavitt-family` shows the defining
   self-similarity relations exist in no `M_n(ZG)` at any finite rank, so
   there is nothing to transport along.  The one surviving crack -- a
   nonunital family in a rank-zero corner -- is itself a hard statement about
   idempotents over `ZG`.
2. **Detect a class in the matrix corona.**  *Dies* immediately:
   `topological-k1-cannot-detect-integral-whitehead`.  The corona's
   topological `K_1` is zero, so the induced map annihilates every algebraic
   class and certifies nothing in either direction.  This is a zero target,
   not a small one.
3. **Route through finitely presented torsion-free groups.**  **Reduction
   completed 2026-08-30.**  The Waldhausen--Higman rope now supplies a
   finitely presented torsion-free host with an injective Whitehead map.
   Together with the recursively-presented finite-support reduction, this
   proves the global conjecture equivalent to
   `whitehead-vanishing-finitely-presented-torsion-free`.  It is a complete
   concentration theorem, not a vanishing proof: the latter node remains
   open.
4. **Farrell--Jones.**  Not attempted here and *deferred*, not refuted: it is
   the only lane with a track record (`degree-one-assembly-surjective-torsion-free`),
   and this graph has none of the controlled-topology machinery it needs.

A fifth non-attempt worth recording because it looks tempting from inside
this program: torsion-free nonsofic and non-MF groups are **not** candidate
counterexamples.  Producing one supplies no matrix, no invariant, and no
reason to expect either.

Full audit, with proofs of everything cited above:
`research/artifacts/whitehead-vanishing-audit-2026-08-17.md`.
