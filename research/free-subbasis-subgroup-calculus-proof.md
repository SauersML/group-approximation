---
rg: 2
id: free-subbasis-subgroup-calculus-proof
kind: route
title: One retraction proves all three facts
target: free-subbasis-subgroup-calculus
requires: []
artifacts:
  - GroupApproximation/Computability/BooneGroupFreeBasis.lean
---

## Direct proof, machine-checked

`retract S : FreeGroup i ->* FreeGroup i` is the lift of the map sending a
basis element to itself if its index is in `S` and to `1` otherwise.

* It fixes `basisSubgroup S` pointwise (`retract_eq_self`), since it fixes the
  generators, and it kills every basis element outside `S`.  So if
  `FreeGroup.of a` lies in `basisSubgroup S` with `a` not in `S`, applying the
  retraction gives `of a = 1`, contradicting `of_ne_one`.  That is
  `of_mem_basisSubgroup_iff`, and `of_ne_one` is itself proved by pushing to
  `Multiplicative Z`.

* Intersection: one inclusion is monotonicity.  For the other, an element of
  both is fixed by `retract S` and by `retract T`, and `retract_mem_inter`
  turns that into membership in `basisSubgroup (S cap T)`.

* Transport: `map_basisSubgroup` is `Subgroup.map_closure` together with the
  image of the basis under the relabelling, and `range_indexMap` is the same
  statement for the whole index map.

No hypothesis on the index set, and no finiteness.
