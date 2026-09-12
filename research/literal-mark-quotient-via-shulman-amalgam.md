---
rg: 2
id: literal-mark-quotient-via-shulman-amalgam
kind: route
title: Route the literal marked quotient through Shulman's amalgam criterion
target: literal-mark-quotient-mf
requires: [shulman-amalgam-mf-criterion, amalgam-edge-compatible-corona-embeddings, literal-lamp-kernel-clifford-block-amalgam]
artifacts:
  - research/artifacts/shulman-2603-13564-verified.md
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
---

## Why sufficient

`literal-lamp-kernel-clifford-block-amalgam` presents the target as
`E/<w> = V *_{B_1} ((Z/2)^8 semidirect B_1)`, and Shulman's Section 2.1
identifies the group amalgam with the C*-amalgam,
`C*(G_1 *_H G_2) = C*(G_1) *_{C*(H)} C*(G_2)`.  With the edge-compatible
embeddings of `amalgam-edge-compatible-corona-embeddings`, Theorem 20 makes
`C*(E/<w>)` MF, and a discrete group embeds in its full group C*-algebra, so
`E/<w>` is MF in the group sense used here.

This is the first route to this claim that is not an exact-finite-model route,
and it is strictly stronger than needed: it concludes MF of the full group
C*-algebra.  Its cost is that both vertex algebras must be MF, and both
contain a property-(T) group.
