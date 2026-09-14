---
rg: 2
id: hyperbolic-group-relative-to-maximal-elementary-subgroup
kind: claim
title: A word-hyperbolic group is hyperbolic relative to the maximal elementary subgroup of each infinite-order element
distinct_from:
  relatively-hyperbolic-dehn-filling: that is the filling theorem for an arbitrary relatively hyperbolic structure; this supplies one particular structure on an ordinary word-hyperbolic group, with a maximal elementary subgroup as its peripheral
---

Let `G` be word-hyperbolic and let `g in G` have infinite order.  Then:

1. `g` lies in a unique maximal elementary subgroup `E(g)` of `G`
   (elementary = containing a cyclic subgroup of finite index);
2. `<g>` has finite index in `E(g)`;
3. `G` is hyperbolic relative to the collection `{ {1}, E(g) }`, in the
   sense of Osin's Definition 1.2 (finite relative presentation with linear
   relative Dehn function).

Clauses 1 and 3 are imported (see the citation route).  Clause 2 is
elementary: `E(g)` is infinite and elementary, so it has an infinite cyclic
subgroup `C` of finite index; some positive power of `g` lies in `C`, so
`<g> intersect C` is a nontrivial subgroup of `C`, hence of finite index in
`C`, hence of finite index in `E(g)`.

**Terminology trap.**  "Hyperbolically embedded" in Osin's 2004 paper means
exactly clause 3: `G` is hyperbolic relative to the old peripheral collection
with `Q` added (his Definition 1.4).  The later Dahmani--Guirardel--Osin notion
of a hyperbolically embedded subgroup is weaker and is not what is used here.
An ordinary word-hyperbolic group is hyperbolic relative to the trivial
subgroup (Osin's Definition 1.2), and relative to that structure every
nonidentity element, in particular every element of infinite order, is
"hyperbolic" in Osin's sense, so Corollary 1.7 applies to every `g` above.

Consumer: `hyperbolic-rf-question-equals-vtf-question-proof`, which fills
`E(g)` by a deep cyclic subgroup.
