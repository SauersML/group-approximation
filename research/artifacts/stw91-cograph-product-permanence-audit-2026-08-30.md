# STW XCI: cograph-product permanence audit

## New class

Let `Gamma` be a nonempty countable graph with no induced four-vertex path and attach
to each vertex an exact group whose reduced tracial C-star algebra is
selfless.  Then the reduced algebra of the graph product is exact and
selfless.

Finite `P_4`-free graphs are precisely cographs.  Their recursive
decomposition uses disjoint union and graph join.  At the group level these
are, respectively, free product and direct product.  The proof therefore
combines two genuinely different permanence inputs:

1. reduced free products of selfless tracial algebras are selfless, with no
   exactness assumption;
2. tensor products of two selfless algebras are selfless when the second
   factor is exact.

Exactness is retained at every finite stage, allowing the operations to be
alternated arbitrarily in the cograph decomposition tree.

For a countable `P_4`-free graph, every finite induced subgraph is a finite
cograph.  Graph-product normal form embeds its group as the subgroup on
those vertices, and all finite stages form a directed union.  Robert's
directed-union permanence finishes the proof.

## Reduced-map audit

No quotient functoriality is used.  Induced-subgraph maps are subgroup
inclusions; restriction of the ambient regular representation is a direct
sum of regular representations of the subgroup, so the reduced maps are
isometric and preserve the coefficient-of-identity trace.

At a disjoint union, the reduced group algebra is the reduced free product
with respect to canonical traces.  At a join, the direct-product regular
representation gives the minimal tensor product.  Thus every algebraic
operation used in the recursion has the exact reduced and tracial meaning
required by selflessness.

## Scope and trust boundary

The theorem includes arbitrary finite and countable mixtures of commuting
and free vertex blocks as long as the commutation graph is `P_4`-free.  It
strictly generalizes the two-factor free-product and direct-product closure
steps as one iterated group construction.

The `P_4`-free hypothesis is structural, not cosmetic.  A general graph
product requires amalgamation over link subgroups when one removes a
vertex, and no corresponding amalgamated selflessness permanence theorem is
used or claimed here.  The result does not prove XCI for vertex groups whose
selflessness is still open.
