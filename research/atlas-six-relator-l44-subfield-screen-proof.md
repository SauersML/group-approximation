---
rg: 2
id: atlas-six-relator-l44-subfield-screen-proof
kind: route
title: Replay every projective seed fiber in both L4(4) subfield marking parities
target: atlas-six-relator-l44-subfield-has-no-marked-pair
requires:
  - atlas-six-relator-relative-small-cancellation-audit
  - atlas-a8-index-44551-to-48960-reaches-l44
artifacts:
  - experiments/atlas_l44_six_relator_screens.py
  - experiments/atlas-six-relator-l44-subfield-screens.json
---

Use the `85`-point projective action of `GL4(4)`.  Its scalar kernel has
order three and its image is `PGL4(4)=PSL4(4)`, so every projective relative
conjugator occurs exactly once.  Embed the certified binary matrix words by
scalar extension and apply the graph automorphism to every factor-two
letter for the second parity.

The first word has the seed form `x A x C x D`.  Enumerate the conjugacy
class of `x`; for every one of its `30` solutions replay the complete
`184320`-element centralizer fiber.  This is an exact partition of all
`5529600` relative conjugators in the parity.  Evaluate the remaining five
words in their certified order and record the first failure.  The two exact
censuses are `(S6L44-2)` and sum to the seed-fiber size.  Both survivor sets
are empty.

