---
rg: 2
id: simple-dedekind-infinite-ring-elementary-full-mf-radical-proof
kind: route
title: A nonzero idempotent in a simple ring is full
target: simple-dedekind-infinite-ring-elementary-full-mf-radical
requires:
  - full-complementary-idempotent-elementary-full-mf-radical
artifacts:
  - non_mf_groups_exist.tex
---

## Why sufficient

Choose `ts = 1 ≠ st`.  Then `e = 1 - st` is a nonzero idempotent, so `ReR` is
a nonzero two-sided ideal of the simple ring `R`, hence `ReR = R`.  This is
the hypothesis of [[full-complementary-idempotent-elementary-full-mf-radical]].
