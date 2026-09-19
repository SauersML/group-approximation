---
rg: 2
id: canonical-types-extend-every-finite-bass-serre-actor
kind: claim
title: Every canonical tracial base type extends through every finite Bass-Serre actor
invalidates:
  - common-nemesis-via-type-specific-hecke-separators
distinct_from:
  finite-packet-graph-atlases-have-a-regular-stationary-flow: that constructs compatible abstract regular multiplicity vectors; this constructs the auxiliary finite groups and HNN stable letters inside the same matrix-ultraproduct factor containing an arbitrary canonical base representation.
  finite-selector-gadget-induction-barrier: that shows every selector character occurs in some representation of a finite overgroup; this proves the much stronger extension statement for the whole canonical base type.
  bespoke-extension-nemesis-library-defeats-diagonal-schedules: that permits arbitrary finite extension gadgets and makes their nonextendability useful; this proves that the subclass consisting only of finite amalgams and finite-subgroup HNN edges has no nonextendability profiles at all.
---

Let `Gamma` be a group and let

```text
theta:Gamma -> U(M)
```

be an exact canonical-trace representation in a tracial matrix-ultraproduct
factor:

```text
tau(theta(g))=0                  for every g!=1.        (CFB1)
```

Let a finite graph of groups have distinguished vertex group `Gamma`, every
other vertex group finite, and every edge group finite.  (This includes HNN
loops identifying finite subgroups of `Gamma`.)  Then `theta` extends to an
exact representation of its fundamental-group presentation in `M`.
Consequently no extension-profile nemesis made only from surrogate finite
actors and finite-subgroup Bass--Serre edges can exclude even one canonical
matrix-ultraproduct base type.

## Proof

For every finite subgroup `A<=Gamma`, `(CFB1)` says that `theta|A` has the
normalized regular character.  Equivalently, the induced embedding

```text
C[A] -> M                                                   (CFB2)
```

is trace preserving for the canonical trace of `C[A]`.

A matrix-ultraproduct factor contains a trace-preserving copy of every
finite-dimensional matrix algebra and hence a trace-preserving regular copy
of `C[K]`.  Its restriction to `C[A]` and `(CFB2)` are two trace-preserving
embeddings of the same finite-dimensional algebra into a finite factor.
Such embeddings are unitarily conjugate: match their minimal central
projections by trace, then match matrix units inside the corresponding
corners.

Choose a maximal tree rooted at `Gamma`.  Proceeding away from the root,
embed each finite vertex group `K` by a regular copy and conjugate that copy
so its parent edge subgroup agrees literally with the already embedded
parent subgroup.  Every finite vertex embedding remains trace preserving.

For a non-tree edge isomorphism `phi:A->B`, the two already constructed
embeddings

```text
a |-> rho_A(a),             a |-> rho_B(phi(a))          (CFB3)
```

again have the normalized regular character, because `phi` is injective.
The same finite-dimensional conjugacy supplies a unitary `u in M` with

```text
u rho_A(a) u^*=rho_B(phi(a))             (a in A),       (CFB4)
```

so assigning the corresponding non-tree stable letter to `u` realizes that
edge.  Repeat for all non-tree edges.  Stable letters not related by an
additional two-cell may be chosen independently, completing the graph-of-
groups presentation.

## Scope

The theorem concerns extension existence, so no faithfulness of the extended
representation is needed.  It applies to every actual canonical embedding,
not only to its scalar word moments or finite-subgroup multiplicity vector.
Rational packet marks and losing atoms do not help: their finite-subgroup
restrictions are still contained in the same regular character.

In particular, for literal finite subgroups `K,H<=Gamma` with an injection
`K->H`, every canonical base type has

```text
tau(e_H)-tau(e_K)=1/|H|-1/|K|<=0.                      (CFB5)
```

This directly rules out the positive global-trace gap requested by
`payload-coupled-hecke-separates-every-marked-ce-extension-type`, even if the
choice of `K,H` depends on the extension type or is described as payload
coupled.  A reverse inequality can occur only after compressing to a
noncanonical selected corner.  The subgroup-HNN actuator does not itself
authenticate or return that corner, so this modification is the original
selected-corner gate rather than a finite-actor solution.

The only possible escape is to add a relation among the auxiliary
intertwiners which is not a graph-of-groups covariance relation, or attach an
infinite/nonamenable actor whose required representation is not freely
available in `M`.  Cycle flatness, a charged proper-corner return, and a
payload-sensitive two-cell are examples of such genuinely non-Bass--Serre
data.  Their construction is exactly the nontransport gate, rather than a
more elaborate finite surrogate actor.
