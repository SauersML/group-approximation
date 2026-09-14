---
rg: 2
id: single-maximal-stage-routed-codes-cannot-compress
kind: claim
title: A code with one combining stage on a Rokhlin-maximal window subgroup, between Borel routings, never compresses
distinct_from:
  bernoulli-codes-descend-to-window-subgroup: that reduces a code whose whole window lies in K to the same problem over K; this allows Borel routing with unbounded displacement before and after the combining stage, so the composite reads every direction of the group and only the combining stage is constrained.
  measurable-certificate-routing-preserves-bernoulli-measure: that shows routing codes alone preserve the measure; this composes routing with one genuinely combining stage and proves the composite still cannot lower the alphabet.
artifacts:
  - research/artifacts/defect-coupled-routed-codes-2026-09-12.md
---

Let `G` be countable, `A = C x D` finite, `K <= G`, and `mu` uniform on `A^G`. Let `R_1` be a routing
code as in `measurable-certificate-routing-preserves-bernoulli-measure`, `S(x)(g) = f((g^-1.x)|_K)`
a Borel code into `E^G`, and `R_2: E^G -> B^G` any Borel equivariant map with `|B| = |E|`.

If `tau = R_2 o S o R_1` is injective on a conull set and the uniform Bernoulli shift over `K` at
alphabet `A` has maximal Rokhlin entropy (or `K` is finite), then `|B| >= |A|`. In particular, if `K`
is sofic, `tau` is not a compression.

**Consequence for `measurable-alphabet-compression-over-leavitt-units`.** The defect-coupling design
"combine symbols locally along the rigid defect, then transport them along the nonamenable actor by
Borel routing" never compresses when the combining window generates a sofic subgroup. A compression
over `U` needs a combining stage whose own window generates a nonsofic subgroup, and synergy spread
over several stages is not covered here.

Proof: Section 2 of the artifact, route `single-maximal-stage-routed-codes-proof`.
