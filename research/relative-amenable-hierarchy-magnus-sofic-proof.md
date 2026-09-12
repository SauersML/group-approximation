---
rg: 2
id: relative-amenable-hierarchy-magnus-sofic-proof
kind: route
title: Unfold each tree action into a level of amenable moves and transport by levels
target: relative-amenable-hierarchy-magnus-one-relator-sofic
requires: []
artifacts:
  - research/artifacts/envelope-relative-hierarchy-characterization-2026-09-11.md
  - research/artifacts/amenable-envelope-magnus-piece-sofic-2026-09-11.md
---

The first artifact, §3, carries the proof.

1. A maximal tree of the countable quotient graph of groups rebuilds `V_i` from
   `V_(i-1)`. The steps are amalgams with sofic vertex groups along amenable edge
   groups, and HNN extensions for the remaining edges. This is one level of a
   leveled envelope.
2. The transport lemma of the second artifact survives directed unions:
   pushouts commute with directed unions, amalgam monotonicity keeps the
   embeddings, and directed unions of sofic groups are sofic. So every Magnus
   truncation embeds in a sofic group, and `G` is sofic.
3. Conversely, from a finite envelope `Y_0 <= ... <= Y_r`, the groups
   `B_0 ∩ Y_i` acting on the move trees form a hierarchy. Side stabilizers lie in
   sofic factors or in conjugates of the sofic groups `Y_(i-1)`.
