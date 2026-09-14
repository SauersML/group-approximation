---
rg: 2
id: some-v-invariant-graph-on-clopen-tuples-is-rado
kind: claim
title: For some Boolean atom pattern of clopen k-tuples, some graph on that tuple sort invariant under Thompson's V is the Rado graph
distinct_from:
  v-invariant-clopen-graphs-are-never-the-rado-graph: that is the case of single clopen sets, decided negatively; this asks for tuples of length k >= 2 and some atom pattern.
  some-fp-group-acts-on-the-rado-graph-with-type-a: that is the host existence question for any finitely presented group; this is the special case G = V on a clopen tuple sort, which implies it.
artifacts:
  - research/artifacts/hl-bh-fraisse-thompson-2026-09-14.md
---

**OPEN.** There are `k >= 2`, a `V`-orbit `X_P` of `k`-tuples of nonempty proper clopen
subsets of the Cantor set, and a `V`-invariant graph on `X_P` isomorphic to the Rado graph.
Here `X_P` is given by its pattern `P` of nonempty Boolean atoms.

## How to attack it

- **Invariant graphs.** Two-element subsets of `X_P` have finitely many `V`-orbits, one for
  each atom pattern of `2k`-tuples (`full-cantor-boolean-atom-orbits-and-embedding-proof`).
  So the invariant graphs are finitely many unions of orbits.
- **Refutation is finite.** The extension property over a family of `K` tuples reduces to
  colourings of the family's atoms, as in Step 2 of `v-invariant-clopen-graph-rado-census-proof`.
  A tuple `z` colours each family atom by the nonempty set of `z`-atoms that meet it. So
  failure at a given `K` is a finite search, SAT-encodable.
- **Proof is not.** Being the Rado graph needs the property for every `K`, so it would need a
  structural argument.

## Status

- `k = 1` is refuted: every invariant graph fails at `K = 3`.
- `k >= 2`: not searched.
