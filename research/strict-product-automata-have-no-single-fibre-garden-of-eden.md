---
rg: 2
id: strict-product-automata-have-no-single-fibre-garden-of-eden
kind: claim
title: Over a surjunctive group times a sofic group, no Garden of Eden pattern of an injective automaton lies in one fibre
distinct_from:
  finite-direct-products-of-surjunctive-groups-are-surjunctive: that is the open unrestricted product statement; this is a proved restriction on any counterexample of product shape with a sofic factor, forcing its Garden of Eden patterns across two fibres.
  products-with-lef-permanence-closure-factors-are-surjunctive: that closes the fibre device through exact finite realizations of the second factor; this uses sofic realizations, pays for the broken decoder with an epsilon fraction of stored input, and closes only for single-fibre Garden of Eden patterns.
artifacts:
  - research/artifacts/product-fibre-garden-of-eden-filter-2026-09-12.md
---

**ESTABLISHED** by `single-fibre-garden-of-eden-transplant-proof`.

**Theorem.** Let `G` be surjunctive, `K` sofic, `A` finite, and `tau` an injective cellular automaton on
`A^(G x K)` with image `X`. Then for every `g in G` and every finite `F <= K`, every pattern on `{g} x F`
is the restriction of a point of `X`.

Equivalently, every Garden of Eden pattern of a strict automaton over `G x K` involves two sites with
different `G`-coordinates.

**Proof idea.**
- Transplant `tau` and its decoder to automata over `G` with alphabet `A^V`, for a sofic model `V` of `K`.
- Store the input on the `epsilon |V|` bad points in an extra track. The transplant becomes injective.
- A single-fibre Garden of Eden pattern is missing from every output column at `c|V|` disjoint places.
  So the output alphabet shrinks by `(1 - q^(-|E|))^(c|V|)`, which beats the stored `q^(epsilon |V|)`.
- The result is an injective automaton over `G` into a smaller alphabet, which contradicts
  surjunctivity of `G`.

Symmetrically, for `G` sofic and `K` surjunctive, Garden of Eden patterns meet two fibres `G x {k}`.

Proof: Sections 1–2 of the artifact.
