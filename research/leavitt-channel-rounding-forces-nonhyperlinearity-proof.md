---
rg: 2
id: leavitt-channel-rounding-forces-nonhyperlinearity-proof
kind: route
title: Round the global heat to select a scalar commutant, then round the native corner heat to find a central height
target: leavitt-channel-rounding-forces-nonhyperlinearity
requires: []
artifacts:
  - research/artifacts/leavitt-uniform-heat-rounding-alone-forces-nonhyperlinearity-2026-09-08.md
  - research/artifacts/leavitt-central-height-and-coordinate-swap-gap-2026-09-08.md
---

Written proof in the two artifacts, independently audited there. The chain
has four steps.

1. Integrated SOS heat estimates make admissible Kazhdan heat maps nearly
   idempotent, so the rounding premise applies.
2. Component selection after rounding the global heat gives a canonical model
   with scalar full `H`-commutant.
3. Rounding the native `L`-heat of that same model and applying the
   quantitative central-height lemma produces a trace-zero central element.
   That lemma rests on block-weight drift under the one-sided inclusion
   `u L u^(-1) < L`.
4. The generation identity `H=<L,uKu^(-1)>` carries this element into the
   centre of the full `H`-commutant, contradicting step 2.

The route adds no new mathematics. It turns the artifact theorem into a
claim that other nodes can require.
