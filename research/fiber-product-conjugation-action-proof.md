---
rg: 2
id: fiber-product-conjugation-action-proof
kind: route
title: Direct computation of the two-sided translation action of a fiber product on the kernel
target: fiber-product-conjugation-action-lemma
requires: []
artifacts:
  - research/artifacts/boone-higman-fiber-product-and-shift-compiler-2026-08-24.md
---

Complete direct proof; it is written out in the target node and uses nothing
beyond the definition of a fiber product.  No Lean counterpart exists.

The only step with any content is the pair-orbit count, and the trick there
is to normalise the first coordinate to `1` before reading off the residual
stabilizer -- after which the residual action is literal conjugation and the
count is forced.
