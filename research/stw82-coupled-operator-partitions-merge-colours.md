---
rg: 2
id: stw82-coupled-operator-partitions-merge-colours
kind: claim
title: Coupled operator partitions subdivide and merge outgoing order-zero colours
artifacts:
  - research/artifacts/stw82-order-zero-spectral-subdivision-audit-2026-08-30.md
distinct_from:
  stw82-quasicentral-cutdowns-repair-to-banded-order-zero: that subdivides one outgoing colour; this couples different subdivisions through cross-colour orthogonality and merges the repaired pieces into fewer global colours.
  stw82-scalar-band-depth-floor: that obstructs independent scalar partitions on one common spectrum; this permits colour-dependent operator-valued partitions and imposes support orthogonality across colours.
---

Fix finite-dimensional C*-algebras `F_v` indexed by a finite set `V`, a
positive integer `d`, and `epsilon>0`.  There is `delta>0` with the following
property.

Let `phi_v:F_v->B` be cpc order-zero maps.  For every `v in V`, suppose
positive contractions `c_(v,1),...,c_(v,d) in M(B)` satisfy

```text
sum_(k=1)^d c_(v,k)=1_(M(B)),                         (C1)
```

and, for every contraction `x in F_v`,

```text
max_k max(
  norm([c_(v,k),phi_v(x)]),
  norm([c_(v,k)^(1/2),phi_v(x)])
) < delta.                                           (C2)
```

Assume the partitions are coupled across distinct original colours by

```text
c_(v,k)c_(w,k)=0             (v!=w, k<=d).           (C3)
```

Then there are cpc order-zero maps

```text
psi_(v,k):F_v->closure(c_(v,k)^(1/2) B c_(v,k)^(1/2))
```

such that

```text
norm(phi_v-sum_k psi_(v,k))<epsilon                  (v in V),
```

and, for each fixed `k`, the direct-sum map

```text
Psi_k:directSum_(v in V) F_v -> B,
Psi_k((x_v)_v)=sum_v psi_(v,k)(x_v),
```

is cpc order zero.

Thus `|V|` outgoing colours can be replaced, without changing their total
action by more than `epsilon` per colour, by `d` global colours whenever such
a coupled operator partition exists.  This is a genuine cross-colour reuse
mechanism; it is not available to independent scalar partitions of unity.
