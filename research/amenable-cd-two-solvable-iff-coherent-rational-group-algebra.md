---
rg: 2
id: amenable-cd-two-solvable-iff-coherent-rational-group-algebra
kind: claim
title: An amenable group of cohomological dimension at most 2 is solvable iff its rational group algebra is left coherent
distinct_from:
  amenable-finite-cd-domain-groups-are-virtually-solvable: that is the domain half in all dimensions, open from dimension 3; this is an established equivalence in dimension at most 2 that trades the domain hypothesis for coherence
  amenable-cd-two-rational-group-algebras-are-coherent: that is the open statement that every such algebra is coherent; this proves it is equivalent to Kropholler's question in dimension at most 2
  characteristic-zero-one-relator-group-algebras-are-coherent: that proves coherence for one-relator groups; this uses it only for the solvable Baumslag--Solitar groups BS(1,m)
---

**ESTABLISHED** through `amenable-cd-two-solvable-iff-coherent-group-algebra-proof`.

Let `G` be an amenable group with `cd_Z G <= 2`. The following are equivalent:

1. `G` is solvable (equivalently virtually solvable; then `G` is `1`, `Z`, a noncyclic subgroup of
   `Q`, or `BS(1,m)` with `m != 0`);
2. `Q[G]` is left coherent;
3. `Z[G]` has no zero divisors.

So Kropholler's question in dimension at most 2 is exactly the statement
`amenable-cd-two-rational-group-algebras-are-coherent`: a minimal two-dimensional counterexample is
an amenable group whose rational group algebra has a principal left ideal that is not finitely
presented, equivalently a finitely generated left ideal with an infinitely generated syzygy.
