---
rg: 2
id: injective-same-alphabet-sofic-codes-preserve-uniform-measure
kind: claim
title: An almost everywhere injective Borel code between equal-alphabet full shifts over a sofic group preserves the uniform measure
distinct_from:
  bijective-ca-preserve-uniform-bernoulli-measure: that assumes a bijective continuous automaton over any group; this assumes only a Borel equivariant code injective on a conull set, over a sofic group.
  every-injective-ca-preserves-uniform-bernoulli-measure: that is the universal continuous statement, equivalent to Gottschalk, whose sofic case goes through Gromov--Weiss bijectivity; this is measurable same-alphabet rigidity over sofic groups, proved by counting on sofic models.
  single-maximal-stage-routed-codes-cannot-compress: that bounds the output alphabet of one combining stage; this also pins the output measure when the alphabet does not grow, which is what lets stages be composed.
artifacts:
  - research/artifacts/non-expanding-sofic-cascades-2026-09-12.md
---

Let `K` be a countable sofic group, `A, B` finite, `mu_A` the uniform product measure, and `S: A^K -> B^K` a
Borel `K`-equivariant map that is injective on a `mu_A`-conull set. Then

1. `|B| >= |A|`;
2. if `|B| = |A|`, then `S_* mu_A = mu_B`.

Part 1 is Rokhlin-maximality of sofic groups (`sofic-radical-localizes-bernoulli-deficit-witnesses`). Part 2
says an equal-alphabet code that is injective almost everywhere is measure preserving, with no continuity and
no bijectivity assumed.

**Proof idea.** Approximate the encoder and the Borel decoder by finite-window functions with error `eps`,
and count on a sofic model `V`.
- Fano's inequality at good points gives `H(y) >= |V|(log q - o(1))`.
- If the output law is not uniform on some finite `F`, with deficit `c > 0`, Shearer's inequality over the
  model translates of `F` gives `H(y) <= |V|(log q - c/|F| + o(1))`.

Full proof: Section 2 of the artifact, route `injective-same-alphabet-sofic-codes-proof`.

**Coset lifting.** For any countable `G` containing `K`, a same-alphabet code over `G` with window in `K` that
is a.e.-injective preserves the uniform measure. This goes through `bernoulli-codes-descend-to-window-subgroup`
and independence over left cosets (artifact, Section 2, Remarks). It is the step that lets the combining stages
of a multi-stage code be composed, in the regime of `measurable-alphabet-compression-over-leavitt-units`.

**ESTABLISHED 2026-09-12** by [[injective-same-alphabet-sofic-codes-proof]]. Verification requested from
w3-vf-nonlinear.
