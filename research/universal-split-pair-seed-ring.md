---
rg: 2
id: universal-split-pair-seed-ring
kind: claim
title: One fixed finitely generated ring is universal for the full-defect hypothesis
distinct_from:
  full-idempotent-ring-has-properly-infinite-unit: that is the equivalence of the manuscript's hypothesis with proper infiniteness of the unit inside a given ring; this exhibits the one ring presented by the splitting relations alone and shows every such ring receives a map from it.
  full-complementary-idempotent-elementary-full-mf-radical: that is the analytic theorem over an arbitrary ring satisfying the criterion; this is the ring-theoretic observation that the criterion has an initial object.
artifacts:
  - research/artifacts/universal-seed-review-2026-09-07.md
  - research/artifacts/universal-seed-model-test-2026-09-07.md
---

Let

```text
C = Z<s_0,s_1,t_0,t_1 | t_i s_j = delta_(ij) 1>,
```

with no relation `s_0t_0 + s_1t_1 = 1`.  Then:

1. `C` is nonzero and of characteristic zero.  It acts faithfully enough on
   the free abelian group on finite binary words, with `s_i` prefixing `i`
   and `t_i` deleting a matching prefix and killing the rest.
2. `C` is finitely generated as a ring, and `EL_n(C)` is finitely generated
   as a group for `n >= 3`.
3. With `e = 1 - s_0t_0`,

   ```text
   t_0 s_0 = 1,      t_1 e s_1 = 1,
   ```

   so `C` satisfies the manuscript's hypothesis with a single-product
   fullness witness.
4. Every unital ring `R` with a properly infinite unit receives a unital ring
   map `C -> R`, sending the generators to any splitting quadruple.  No
   injectivity is claimed or needed.

So the class of rings satisfying the manuscript's hypothesis has `C` as an
initial object for the purposes of the elementary-group theorems.
