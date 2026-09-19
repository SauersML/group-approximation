---
rg: 2
id: atlas-full-large-rectangle-has-no-a8-a10-quotient
kind: claim
title: The full large-rectangle forward-collision group has no A8, A9, or A10 quotient
artifacts:
  - experiments/atlas_a4_full_large_rectangle_simple_quotients.g
  - research/artifacts/atlas-a4-full-large-rectangle-a8-a10-screen.json
distinct_from:
  atlas-a8-carrier-reaches-third-large-core-edge: that gives a marked A8 quotient before the fourth edge; this proves the fourth edge removes every epimorphism to A8 and also excludes the next two alternating targets.
---

For the universal group consisting of the complete large `K_(2,2)` rectangle,
collision, and 144-state forward fan, exact GAP `GQuotients` computations find
no epimorphism onto `A8`, `A9`, or `A10`.  The counts are zero before imposing
the marked vertex-order filter.

Thus the order-seven failure of the known A8 carrier is not an artifact of
that one marking: no alternative A8 marking works.  Enlarging the natural
alternating degree through ten also does not produce a finite carrier.  This
is a bounded finite-simple exclusion, not a proof that the universal group has
no finite quotient.

