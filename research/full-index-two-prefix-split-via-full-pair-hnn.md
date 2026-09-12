---
rg: 2
id: full-index-two-prefix-split-via-full-pair-hnn
kind: route
title: Extend the Reynolds edge over its companion sign and reuse it as the pulse edge
target: full-index-two-hnn-edge-creates-own-prefix-split
requires:
  - index-two-reynolds-hnn-is-a-proper-corner-section
  - finite-depth-prefix-preserving-hard-sign-hnn
---

Replace the smaller associated subgroup in the one-sided Reynolds section by
the full marked index-two source `C_0=<H_0,J>`, and take as target the full
marked pair `C_1=<H_1,B>`.  The pair isomorphism sends `J` to the very pulse
sign `B` used by the first-hit ledger and fixes every earlier pulse sign.
Reynolds averaging then gives the positive retained range and negative
companion formulas in `full-index-two-hnn-edge-creates-own-prefix-split`.

This route changes only the one-source edge.  It does not assert that all
retained Schur types have already been organized into compatible full-pair
sources; that is the remaining global ledger in
`balanced-schur-active-child-is-next-prefix-source`.
