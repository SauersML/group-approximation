---
rg: 2
id: iwahori-exact-first-blocks-proof
kind: route
title: Combine the projection normal form, density bound, and stable block rounding
target: iwahori-counterexample-has-exact-first-vertex-blocks
requires:
  - iwahori-transfer-failure-reduces-to-two-block-projection
  - iwahori-transfer-failure-has-two-positive-density-blocks
  - stable-representation-block-rounding
  - sl2-z-same-dimension-hs-stable
---

The first two requirements give an almost-reducing cut with both physical
blocks bounded below.  Stable block rounding makes the first vertex exactly
reduce that same cut.  All changes vanish in normalized HS norm, so the edge
and second-vertex inequalities survive.
