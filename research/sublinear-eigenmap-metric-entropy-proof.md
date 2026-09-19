---
rg: 2
id: sublinear-eigenmap-metric-entropy-proof
kind: route
title: Turn shrinking metric-entropy clusters into Fourier packets
target: sublinear-eigenmap-metric-entropy-implies-uniform-gamma
requires:
  - asymptotically-clustered-diagonal-ah-has-uniform-gamma
artifacts:
  - research/artifacts/stw99-xx-eigenmap-metric-entropy-2026-08-30.md
---

Fix a stage `n`, a finite test set `F`, and `k>=2`.  Choose `m_j` and
`delta_j` as in `(ME1)`.  Cover the eigenmap multiset at stage `m_j` by

```text
N_j=N_(n,m_j)(F,delta_j)
```

balls.  Assign every eigenmap copy to one ball containing it, breaking
ties arbitrarily.  This turns the cover into a partition by at most `N_j`
clusters.  Two eigenmaps assigned to the same cluster have `d_F`-distance
at most `2 delta_j`.

Within each cluster, group as many indices as possible into disjoint
`k`-element packets.  Fewer than `k` indices remain in each cluster, so the
total remainder `R_j` satisfies

```text
|R_j| <= (k-1)N_j,
|R_j|/L_(n,m_j) -> 0.                                (ME2)
```

Every resulting packet has diameter at most `2 delta_j` on `F`, which tends
to zero.  Equations `(ME1)--(ME2)` are exactly the asymptotic packetability
hypothesis of `asymptotically-clustered-diagonal-ah-has-uniform-gamma` for
this `n`, `F`, and `k`.  Since the entropy hypothesis holds for every early
stage and finite test set, that theorem supplies norm-central Fourier
partitions with uniform mixed-trace splitting for every `k`.  Hence `A` has
uniform property Gamma.

The cofinality in `(ME1)` is used only to make these choices beyond every
previous diagonalization stage.  The sequence is allowed to depend on
`n` and `F`; a single subsequence working simultaneously for all tests is
not assumed.
