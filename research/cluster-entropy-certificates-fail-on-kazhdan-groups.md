---
rg: 2
id: cluster-entropy-certificates-fail-on-kazhdan-groups
kind: claim
title: No splitting-monotone cluster entropy functional certifies Bernoulli Rokhlin maximality on an infinite Kazhdan group
distinct_from:
  cluster-entropy-functionals-vanish-on-one-ended-bernoulli: that is the general statement for one-ended groups; this specializes it to infinite property (T) groups, the hosts of bernoulli-rokhlin-maximal-on-fg-simple-kazhdan-groups.
  bernoulli-rokhlin-maximal-on-fg-simple-kazhdan-groups: that is the open maximality statement; this rules out one class of lower-bound mechanisms for it.
artifacts:
  - research/artifacts/cluster-entropy-functionals-one-ended-obstruction-2026-09-17.md
---

Let `G` be an infinite group with property (T), with a finite symmetric generating set. For every
cluster functional `F(Q) = sum_W c_W H(join_{w in W} w^-1 Q)` that is splitting-monotone on
Bernoulli coordinate partitions, and every Bernoulli shift over `G`,
`lim sup_n F(Q_{B_n}) <= 0`. In particular no Bethe or Kikuchi relative of Bowen's f-invariant
proves `h^Rok = log|A|` on any host of `bernoulli-rokhlin-maximal-on-fg-simple-kazhdan-groups`,
whatever its windows and weights.

**ESTABLISHED 2026-09-17** by [[cluster-entropy-certificates-fail-on-kazhdan-groups-proof]].
