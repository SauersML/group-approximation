---
rg: 2
id: rokhlin-maximality-closed-under-local-embeddings
kind: claim
title: A group locally embeddable into Rokhlin-maximal groups is Rokhlin-maximal
distinct_from:
  bernoulli-rokhlin-deficit-has-a-finitary-witness: that computes Rokhlin entropy through finite configurations and gets closure under directed colimits and canonical hosts; this is closure under injective partial multiplication tables, which contains both and applies to groups that are not colimits of maximal groups.
  bernoulli-rokhlin-maximality-passes-to-subgroups: that transfers maximality down to subgroups and up finite index; this transfers it along local embeddings into other groups.
  lef-lamp-graph-wreaths-are-surjunctive: that proves surjunctivity is closed under local embeddings and applies it to LEF lamps; this proves the entropy version, which needs only the products of the configuration and no missing cylinder.
artifacts:
  - research/artifacts/kun-thom-wreath-rokhlin-test-case-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

Say `H` locally embeds into a class `C` when every finite `S ⊂ H` containing `1` has an injective
`η: S -> K`, for some `K` in `C`, with `η(ab) = η(a)η(b)` whenever `a, b, ab ∈ S`. If every group
in `C` is Rokhlin-maximal at `q`, meaning uniform Bernoulli shifts over it have Rokhlin entropy
equal to base entropy, then so is `H`.

*Proof sketch.* A configuration `(k, E, F, ψ)` has `Φ` determined by the incidence pattern of the
products `fe` and `1`. An injective partial multiplication map on `{1} ∪ E ∪ F ∪ FE` preserves that
pattern in both directions, so a deficit over `H` would be a deficit over some `K` in `C`. Section 2
of the artifact.

**Consequence (LEF lamps).** By Lemma 4.1 of
`research/artifacts/lef-graph-wreath-surjunctivity-2026-09-12.md`, a graph wreath `Λ(A) ⋊ G` with `A`
LEF locally embeds into graph wreaths `Λ(B) ⋊ G` with `B` finite, over the same actor and graph. So
Rokhlin-maximality of all finite-lamp graph wreaths over `G` gives it for every LEF lamp. The
Kun–Thom test case `kun-thom-wreath-bernoulli-rokhlin-maximal` with any LEF lamp reduces to finite
lamps.

**ESTABLISHED 2026-09-12** by [[rokhlin-maximality-local-embeddings-proof]].
