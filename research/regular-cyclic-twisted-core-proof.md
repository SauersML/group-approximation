---
rg: 2
id: regular-cyclic-twisted-core-proof
kind: route
title: Combine the twisted-group finiteness criterion with an effective integer-coordinate brick calculus
target: regular-cyclic-twisted-core-is-decidable-mif-non-fp
requires: [twisted-brin-thompson-finite-presentation-criterion]
artifacts:
  - research/artifacts/boone-higman-relative-automorphism-fp-obstruction-2026-09-08.md
---

Use Omega=Z with its regular translation action. Finite generation follows
from Belk--Zaremsky Theorem A, since the actor Z is finitely generated
and has one orbit. Simplicity is their Theorem 3.4. Global coordinate
shifts give an embedded copy of Z, so the group is infinite. These are
imports from [Twisted Brin--Thompson groups](https://eprints.gla.ac.uk/280398/1/280398.pdf).

All twisted Brin--Thompson groups are highly transitive, and every finitely
generated highly transitive simple group is MIF. Both statements, with
their source references, are given in the introduction of
[BFFHZ](https://arxiv.org/html/2503.21882v2), immediately before Theorem C.
They imply that this particular group is MIF.

For non-finite-presentability, unordered pairs {i,j} have the invariant
|i-j| under translations. Every positive integer occurs, so there are
infinitely many pair orbits. The necessary direction of
`twisted-brin-thompson-finite-presentation-criterion` therefore excludes a
finite presentation. The other type-(A) conditions hold for the actor:
Z is finitely presented, the action is faithful, and point stabilizers
are trivial.

Here is the effectivity argument for this particular group. Use the finite
brick descriptions in Belk--Zaremsky Section 1. A brick B(u) is specified
by a finite-support function u:Z->{finite binary words}; its points have
the prescribed prefixes. Write h_u for prefix insertion. Each branch of
an element is encoded by (u,v,k) and has the form

    h_v tau_k h_u^-1 : B(u) -> B(v),
    tau_k(z)(j)=z(j-k),       k in Z.

Finite lists of branches have source and target partitions of the whole
Cantor cube. All integers and words in this description are finite data.

To compose two diagrams, intersect each range brick of the first with
each source brick of the second. In each coordinate, prefix cylinders
are disjoint or their intersection is the one with the longer prefix.
Only finitely many coordinates occur. Pulling a resulting sub-brick back
through a branch requires only an integer shift of coordinates and
insertion or deletion of finite prefixes. Restrict both branches to these
sub-bricks and compose; their shift labels add. This gives an effective
finite diagram for the product. Inversion reverses each branch and
negates its shift label.

Identity is decidable directly from any resulting diagram. A branch
with k!=0 cannot be the identity on its source brick: choose j outside
the finite supports of v and the k-shift of u. Its output coordinate j
is then the unrestricted input coordinate j-k, which can be chosen
independently of input coordinate j. A branch with k=0 is the identity
on B(u) exactly when u=v. Indeed, coordinatewise the equality
u(j)w=v(j)w for every infinite binary suffix w forces the two finite
prefixes to be equal. Thus a diagram is the identity exactly when each
branch has k=0 and u=v.

Fix any finite generating set, whose existence was established above.
Its elements have finite brick descriptions, which can be included as
constants in an algorithm. The preceding operations decide any word in
these generators. Enumerating all words and retaining the words that
evaluate to the identity gives a recursive relator set presenting the
group on that generating set.

The finiteness and MIF statements are citation imports; the specialization
of the word algorithm is written explicitly here. None is claimed to be
Lean-verified, and decidability supplies no finite relator bound.
