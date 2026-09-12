---
rg: 2
id: separating-repetitive-amenable-schreier-families-force-soficity
kind: claim
title: Subgroups with repetitive amenable Schreier graphs that separate every finite set make the group sofic
distinct_from:
  hamming-transports-of-weak-sofic-models-are-soficity: that says finite actions carrying weakly sofic models with uniform separation give soficity; this starts from exact infinite coset spaces, where separation holds only at a positive-density set of vertices depending on the finite set, and bounds the reach of the fixed-configuration transfer.
  repetitive-amenable-schreier-fixed-configurations-lie-in-image: that places fixed configurations of one such subgroup in every injective image; this shows that obtaining every configuration this way, for every alphabet, needs a family that already makes the group sofic or locally embeddable into surjunctive groups.
artifacts:
  - research/artifacts/subgroup-fixed-configuration-transfer-2026-09-12.md
---

**ESTABLISHED** by `schreier-family-amplification-proof`.

**Theorem.** Let `G` be a group. Suppose that for every finite `F <= G` containing `1` there is a
subgroup `H_F` with `H_F cap F F^-1 = {1}` whose Schreier graph `H_F\G`, labelled by `D = F cup F^-1`,
has a Følner sequence along which the rooted labelled 1-ball of the base vertex `H_F` has positive
lower density. Then `G` is sofic.

**Reach of the fixed-configuration transfer.** Theorems A and B of the artifact place `Fix_H` in the
image of every injective automaton when `H` has finite index, or has a repetitive amenable Schreier
graph, or is normal with a surjunctive quotient. Surjectivity over every alphabet by density of these
configurations needs, for each finite `F`, an admissible `H` separating `F` into distinct cosets. That
is the case of the pattern taking `|F|` distinct values.
- If subgroups of the first two kinds separate cofinally, the theorem makes `G` sofic.
- Otherwise normal subgroups with surjunctive quotients separate every large finite set. Then `G` is
  locally embeddable into surjunctive groups, and `strict-pairs-transfer-to-table-realizations` already
  applies.

So the transfer decides surjunctivity outright only on groups that existing theorems already cover. On
every other group it yields filters on Garden of Eden patterns, and nothing more.

Proof: Section 3 of the artifact.
