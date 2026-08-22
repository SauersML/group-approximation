---
rg: 2
id: atlas-full-large-rectangle-has-no-screened-small-simple-quotient
kind: claim
title: The full large-rectangle group has no quotient onto nine screened small simple targets
artifacts:
  - experiments/atlas_a4_full_large_rectangle_simple_quotients.g
  - research/artifacts/atlas-a4-full-large-rectangle-small-simple-screen.json
distinct_from:
  atlas-full-large-rectangle-has-no-a8-a10-quotient: that excludes the first three alternating targets; this extends the exact epimorphism screen to the natural low-order classical and sporadic candidates.
---

Exact `GQuotients` computations find no epimorphism from the universal full
large-rectangle, collision, and forward-fan group onto any of

```text
A8, A9, A10, PSL3(4), PSU3(3), PSp4(3), M11, M12, Sp6(2).
```

Every count is zero before marked vertex-order filtering.  These targets
include the natural small simple groups whose orders can accommodate the four
finite vertices (apart from `PSU3(3)`, which is independently excluded because
60 does not divide 6048).  This is a finite target screen, not a no-finite-
quotient theorem.

