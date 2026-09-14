---
rg: 2
id: products-with-lef-factors-preserve-surjunctivity
kind: claim
title: The direct product of a surjunctive group with an LEF group is surjunctive
distinct_from:
  free-centralizer-amalgams-are-surjunctivity-inert: that amalgamates a free LEF centralizing factor over a subgroup, giving free-product kernels; this is the direct product with an LEF factor, proved by partial-table embeddings into finite-index overgroups of the surjunctive factor.
  lef-lamp-graph-wreaths-are-surjunctive: that is the permanence theorem for graph wreaths with LEF lamps over a surjunctive actor; this is the plain direct product, where the LEF group is a factor rather than a lamp, and the proof is table transfer rather than peeling.
artifacts:
  - research/artifacts/surjunctivity-closure-properties-2026-09-12.md
---

Let `G` be surjunctive and `K` locally embeddable into finite groups (LEF). Then `G x K` is surjunctive.
In particular `G x K` is surjunctive for every residually finite `K`, for example `G x Z^d` or `G x F_n`.

**Proof idea.** A finite subset of `G x K` embeds as a partial multiplication table into `G x L` with `L`
finite, by the identity on `G` times a local embedding of its `K`-projection. `G x L` is a finite-index
overgroup of `G`, so it is surjunctive by `surjunctivity-is-a-commensurability-invariant`. Corollary 1 of
`strict-pairs-transfer-to-table-realizations` finishes. Section 2 of the artifact has the proof.

**General form.** `G x K` is surjunctive whenever every finite subset of `K` embeds as a partial table into
some `L` with `G x L` surjunctive.

**Consequence.** Products of the known surjunctive nonsofic witnesses are surjunctive. The product of two
permutational wreaths with residually finite lamps and bases is again one, over the product base.
