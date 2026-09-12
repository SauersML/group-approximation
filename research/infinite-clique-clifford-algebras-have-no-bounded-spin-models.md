---
rg: 2
id: infinite-clique-clifford-algebras-have-no-bounded-spin-models
kind: claim
title: Over a finite field, Clifford algebras of graphs with an infinite clique have no bounded-support model in any infinite tensor product of matrix algebras
invalidates: [kun-thom-clifford-skew-rings-sf-from-matrix-lamp-wreath]
distinct_from:
  oriented-clifford-skew-rings-embed-in-matrix-lamp-wreath: that embeds every orientable graph into the matrix-lamp wreath by Pauli strings of bounded support; this proves no such bounded-support realization exists once the graph has an infinite clique, so the complete graph is out of reach of that embedding.
  nondegenerate-clifford-skew-rings-have-no-finite-dim-reps: that rules out finite-dimensional targets; this rules out bounded-support local targets inside simple infinite tensor products.
artifacts:
  - research/artifacts/clifford-skew-ring-matrix-lamp-wreath-2026-09-12.md
---

Let `k` be a finite field of odd characteristic, `n >= 1`, and `X'` any set. In the restricted tensor
product `tensor_(X') M_n(k)`, every family of pairwise anticommuting elements with invertible squares and
supports of bounded size is finite.

**Consequences.**
- **No local models.** If a `G`-invariant graph `S` has an infinite clique, as the complete graph does,
  there is no homomorphism from its Clifford algebra into any such tensor product that sends the generators
  to elements of bounded support. When `G` has finitely many orbits on the sites, this covers every
  equivariant map.
- **The matrix-lamp route stops short of the complete graph.** Stable finiteness of
  `matrix-lamp-wreath-algebras-are-stably-finite` settles the oriented covers, but by this kind of embedding
  cannot reach the complete-graph Clifford cover of the Kun--Thom pair.
- **Hierarchy.** The complete-graph skew ring sits at the top.

**ESTABLISHED 2026-09-12** by `infinite-clique-no-bounded-spin-models-proof`.
