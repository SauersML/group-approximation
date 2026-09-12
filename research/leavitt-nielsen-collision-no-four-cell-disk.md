---
rg: 2
id: leavitt-nielsen-collision-no-four-cell-disk
kind: claim
title: The collided Leavitt candidate has no paired coefficient-kernel disk through four cells
artifacts:
  - research/leavitt-nielsen-collision-no-four-cell-disk-proof.md
  - research/artifacts/verify-leavitt-nielsen-collision-four-cell.py
distinct_from:
  leavitt-nielsen-collision-has-a-hidden-first-side-relation: that gives a long identity in the first corner map but no outer boundary; this exhausts the first possible small paired pictures and proves none supplies the missing boundary.
---

All 2,620 reduced planar four-cell colorings fail to close.  The four
maximal cases have two duplicate-gate digons and one residual internal label,
up to rotation/inversion.  That label expands to the nonempty normal form

```text
a_1 | q_0 | e_1 | (p^(-1)a)_0 | (pq)_1 | a_0
```

in `G_0*G_1`.  Thus the first-side Nielsen collision does not yield an actual
KL coefficient boundary at area four.
