---
rg: 2
id: ugc-from-rich-2to1-via-bkm-equivalence
kind: route
title: Transport Rich 2-to-1 hardness across the Braverman--Khot--Minzer equivalence
target: unique-games-conjecture
requires: [rich-2to1-games-conjecture, rich-2to1-conjecture-is-equivalent-to-ugc]
---

Immediate.  `rich-2to1-conjecture-is-equivalent-to-ugc` is the published
equivalence, so a proof of `rich-2to1-games-conjecture` transports across
it to `unique-games-conjecture`.

Both premises are listed on purpose.  The equivalence is a literature
import and must stay visible as one; a route reading `requires:
[rich-2to1-games-conjecture]` alone would hide the citation inside an
asserted arrow, and a later reader would have no way to see that the step
is somebody else's theorem rather than this repository's.

Note also that the equivalence runs both ways, so this route carries no
loss: working on the rich formulation is not a weakening, only a change of
where the difficulty is concentrated.
