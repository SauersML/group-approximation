---
rg: 2
id: atlas-hs-s8-derived-packet-collision-exclusion-proof
kind: route
title: Screen the five HS/S8 double cosets with the sixteen directed packet edges
target: atlas-hs-s8-derived-packet-collision-exclusion
requires:
  - atlas-a8-index-991-to-2200-reaches-hs-s8-derived
  - atlas-a4-19243-classical-collapse
---

The official degree-1100 ATLAS action whose point stabilizer has derived
subgroup `A8` identifies the required maximal `S8` class.  Stabilizer orbits
give the five subdegrees in `(HSD1)`, and orbit representatives give the
intersection and generation data by exact GAP group operations.

For the marked screen, the official degree-100 action and ATLAS maximal-
subgroup word construct the same `S8` class.  Map every `GL4(2)` label in the
packet, collision, and q14 words into its derived `A8`.  Preserve the free-
factor coordinate when deduplicating the thirty pair cubes; this leaves
sixteen directed edges.

For one edge `(x y^g)^3=1`, enumerate the ambient conjugacy class of `y` and
then its centralizer fiber.  This visits every `g in HS` exactly once.  Test
the remaining fifteen edges and, for each survivor, record
`|M intersection M^g|`; the five possible values from the independent
double-coset calculation identify the cell.  Finally evaluate collision
19243 and q14 by literal word multiplication.  The exact totals are `(HSD2)`.

All calculations are finite permutation-group arithmetic.  The artifact
assertions fix the group orders, five subdegrees, intersection types,
sixteen factor-oriented edges, survivor table, and collision-value order
histogram, so a replay fails rather than silently reverting to the invalid
twelve-edge unoriented screen.

