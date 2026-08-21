---
rg: 2
id: iwahori-question-from-infinitesimal-rigidity-and-far-sector
kind: route
title: Newton iteration near the compatible locus, outlier repair away from it
target: iwahori-local-global-defect-question
requires:
  - iwahori-newton-closes-near-sector
  - iwahori-outlier-repair
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
---

Split the pairs `pi` of modular representations by their distance to the
compatible locus.  Near it, uniform infinitesimal rigidity plus
dimension-free second-derivative bounds run a Newton--Kantorovich iteration
that converges to a compatible pair within `K def(pi)`.  Away from it, the
full-rank outlier repair of the `iwahori` lane is the claimed mechanism.
This route only records that the two halves are complementary; it adds
no proof of either.
