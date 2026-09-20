---
rg: 2
id: block-permuting-local-fixers-force-disjoint-supports
kind: claim
title: Local fixers that permute a common finite partition cannot live in a torsion-free group with cyclic centralizers
distinct_from:
  locally-fixed-torsion-free-subgroups-of-v-have-disjoint-supports: that is the general compression lemma (OPEN); this proves it when the local fixers can be chosen to permute the fixed pieces, which covers the torsion-free analogue of the S_3 calibration example.
  one-ended-hyperbolic-subgroups-of-v-are-locally-fixed: that handles the case of a north–south element; this handles block-permuting fixers, a disjoint case (elements permuting a finite partition can still contract inside blocks).
artifacts:
  - research/artifacts/gq-bh-scout-bbmz-ranked.md
---

**ESTABLISHED** by `block-permuting-local-fixers-disjoint-supports-proof` (lane proof, bh-scout-bbmz, 09-19, not
reviewed). It is elementary, and nothing about `V` is used.

**Lemma B.** Let `Γ` be a torsion-free group acting faithfully on a set `C`, in which commuting nontrivial elements lie in
a common cyclic subgroup. Torsion-free hyperbolic groups are an example. Suppose `C = W_1 ⊔ … ⊔ W_m` with `m ≥ 2`, and
let `h_1, …, h_m ∈ Γ ∖ {1}` satisfy:
- `h_i` is the identity on `W_i`;
- each `h_i` permutes the set of pieces `{W_1, …, W_m}`.

Then this is impossible: no such configuration exists.

**Consequence for the decisive three-cone test** (`locally-fixed-torsion-free-subgroups-of-v-have-disjoint-supports`).
Let `x_AB, x_BC, x_AC ∈ V` each fix the third cone pointwise and map cones onto cones. For example, take "labeled
transpositions" swapping two cones through elements of `V`, the torsion-free analogue of the `S_3` counterexample.
Then `⟨x_AB, x_BC, x_AC⟩` is never torsion-free with cyclic centralizers, and in particular never free.

**Consequence for (COMP).** (COMP) holds for every `Γ ≤ V` whose local fixers can be chosen to permute a common finite
partition by their fixed pieces. What is left open is only local fixers that mix pieces, e.g. `x_AB` mapping `A` onto a
proper part of `A ∪ B` that is neither `A` nor `B`.
