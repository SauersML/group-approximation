---
rg: 2
id: oyakawa-graph-wreath-rf-iff-acting-group-rf
kind: claim
title: Oyakawa's hyperbolic graph-wreath products are residually finite exactly when the acting group is
invalidates:
  - non-rf-hyperbolic-via-oyakawa-graph-wreath
distinct_from:
  needham-graph-wreath-rf-criterion: that is the imported general criterion, three conditions on an arbitrary action of an arbitrary group on an arbitrary graph; this discharges all of them from properness, local finiteness and finiteness of the lamp group, and so is a statement about Oyakawa's hyperbolic family specifically
  oyakawa-graph-wreath-hyperbolic: that is the imported hyperbolicity statement; this is the residual-finiteness consequence, and its point is that the family cannot contain the first counterexample
artifacts:
  - research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md
---

Under the hypotheses of Oyakawa's Corollary 1.4 — `X` a locally finite
hyperbolic graph of girth `> 20`, `G` acting properly and cocompactly, `H`
finite and nontrivial — the hyperbolic graph-wreath product satisfies

```text
X(H) ⋊ G  is residually finite   <=>   G  is residually finite.
```

## Consequence: this family cannot produce the first counterexample

Oyakawa records that residual finiteness of these groups "might shed light on
the long-standing open problem asking whether every hyperbolic group is
residually finite".  The equivalence answers that for the proper-cocompact
case, negatively: if `X(H) ⋊ G` fails residual finiteness then `G` fails it,
and `G` — acting properly and cocompactly on a locally finite hyperbolic
graph, which is a proper geodesic space — is quasi-isometric to that graph by
Milnor--Švarc and hence is itself a word-hyperbolic group.  So a
counterexample in this family always contains a smaller counterexample that
was there first.  New hyperbolic groups, no new residual-finiteness
behaviour.

## What is not closed

The **relative** construction, Oyakawa's Theorem 1.3, where the graph is only
fine, edge stabilizers are finite and vertex stabilizers merely finitely
generated.  There properness fails, the finiteness arguments that discharge
Needham's conditions fail with it, and the output is relatively hyperbolic
rather than hyperbolic.  That case is discussed on
`non-rf-hyperbolic-via-oyakawa-graph-wreath` and is not claimed either way
here; note only that combining it with the filling route would additionally
require every Oyakawa peripheral to be residually finite while Needham's
conditions fail, which is a strong separability statement in its own right.
