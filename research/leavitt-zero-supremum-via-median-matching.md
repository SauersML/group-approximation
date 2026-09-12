---
rg: 2
id: leavitt-zero-supremum-via-median-matching
kind: route
title: Turn the median component matching of the nine-leaf configuration into a Bernoulli deficit certificate
target: leavitt-units-have-zero-rokhlin-entropy-supremum
requires: [openai-bounded-median-component-matching, leavitt-units-carry-nested-rigid-defect, median-matching-transfers-to-bernoulli-partitions]
artifacts:
  - research/artifacts/median-matching-entropy-translation-2026-09-12.md
  - research/artifacts/gk-verify-pos-permanence-chain-2026-09-12.md
---

**Dead.** The plan was to rebuild the step that sees the nonsoficity of `U` as partition counting over
`U` itself:
- run the median normalization and the injective component matching on the partition process of a
  configuration;
- use the nested defect as the fold that the localization theorem requires;
- let a decoder that is correct almost everywhere absorb the exceptional set.

That needs the transfer in the third prerequisite: Kazhdan components on the shift, or a finite set the
generators permute. `median-matching-has-no-bernoulli-entropy-analogue` refutes the transfer and
invalidates this route. On the shift every `Gamma`-invariant observable is constant. On a finite piece
of `U` the boundary has the order of its size.

The device's usable output, invisibility of the defect in finite models, is necessary for a deficit and
is already on record. No step of the device constructs a partition. Section 3 of the artifact says what
a construction would still need.

Verified 2026-09-12 by gk-verify-pos (Section 26 of the verification artifact). The refutation of the
third prerequisite is sound. This route is the only node requiring it, so invalidating it removes no
viable implication. The target stays open.
