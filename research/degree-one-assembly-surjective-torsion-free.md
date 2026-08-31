---
rg: 2
id: degree-one-assembly-surjective-torsion-free
kind: claim
title: Degree-one assembly is surjective for every torsion-free group
distinct_from:
  whitehead-vanishing-torsion-free: that is the vanishing of a quotient of K_1(ZG); this is surjectivity of a map into K_1(ZG). They are equivalent, by whitehead-is-degree-one-assembly-cokernel, but this is the form in which the literature actually proves cases, so the two are worth carrying separately.
  whitehead-is-degree-one-assembly-cokernel: that claim identifies the cokernel of this map for *every* group and is established; this claim asserts that the map is onto for torsion-free groups and is open. One computes an invariant, the other conjectures its vanishing.
  torsion-free-countable-non-mf: that asks for a torsion-free group failing an operator-algebraic approximation property; this asserts surjectivity of an algebraic K-theory assembly map for all torsion-free groups. Only the words "torsion-free" are shared -- see whitehead-vanishing-torsion-free on why neither property bears on the other.
  torsion-free-finitely-presented-non-mf: that is this program's root about non-MF groups; this is an algebraic K-theory statement quantified over all torsion-free groups, with no approximation content and no finite-presentation hypothesis.
  torsion-free-higman-embedding: that embeds recursively presented torsion-free groups into finitely presented ones and is pure combinatorial group theory; this is a surjectivity statement about assembly maps in algebraic K-theory.
artifacts:
  - research/artifacts/whitehead-vanishing-audit-2026-08-17.md
---

For every torsion-free group `G` the degree-one assembly map

    A_1^G : H_1(BG; K(Z)) -> K_1(ZG)

is surjective.

This is where the real work on `whitehead-vanishing-torsion-free` has always
happened.  It is implied by the `K`-theoretic Farrell--Jones conjecture, and
is therefore **known** for Lueck's Farrell--Jones class: hyperbolic groups,
finite-dimensional CAT(0)-groups, lattices in virtually connected Lie groups,
fundamental groups of manifolds of dimension at most three, and S-arithmetic
groups (arXiv:2507.11337, class `FJ`; read at survey level, not from the
individual proofs).

Attacking it *through* Farrell--Jones has a structural advantage this graph
should not lose sight of: the full conjecture is inherited under subgroups
and directed colimits, and the bare assertion `Wh = 0` is not.  That
asymmetry is exactly why Lueck's reduction of Farrell--Jones to one universal
finitely presented group works, while the analogous packaging for Whitehead
vanishing (`whitehead-vanishing-universal-test-group`) buys nothing.

Open in general.  No route here; the node exists to record that the FJ lane,
not the operator-algebraic lanes, is where a proof would come from.

## Attempts

**Deferred, deliberately, and this is the one lane where that is the right
call.**  Every known case is proved by controlled topology -- Farrell--Hsiang
transfer arguments, flow spaces for CAT(0) and hyperbolic groups, geodesic
flow estimates -- and each such proof is engineered for its geometry rather
than derived from a general principle.  Nothing in this repository builds
classifying spaces or flow spaces, so attacking it here would mean starting
that machinery from nothing.

Where a *general* attack dies, for the record: the class `FJ` is closed under
subgroups, finite products, free products and directed colimits, which is why
Lueck can reduce the full conjecture to one universal finitely presented
group.  Trying to run the same reduction for the bare degree-one statement
fails at the colimit step, because surjectivity of assembly in one degree is
not inherited by colimits in the way the full conjecture's isomorphism
statement is.  That asymmetry is the reason the packaging trick that works
for Farrell--Jones does not work here, and it recurs one level down at
`whitehead-vanishing-universal-test-group`.
