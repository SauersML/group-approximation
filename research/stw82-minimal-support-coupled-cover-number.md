---
rg: 2
id: stw82-minimal-support-coupled-cover-number
kind: claim
title: Operator subdivision of minimal supports still has chromatic label capacity
artifacts:
  - research/artifacts/stw82-support-hall-capacity-audit-2026-08-30.md
distinct_from:
  stw82-indivisible-order-zero-reuse-is-graph-colouring: that forbids splitting the outgoing maps; this allows arbitrary positive operator-valued cutters and proves that exact support-local subdivision still cannot beat graph colouring for minimal supports.
  stw82-spectral-support-hall-capacity: that gives necessary tracial Hall inequalities; this computes the exact cover number for minimal supports and shows those inequalities are not sufficient.
---

Let `M` be a finite-dimensional C*-algebra and let `(p_v)_(v in V)` be a
finite family of minimal projections.  Form the graph `G_p` by joining
distinct `v,w` when

```text
p_v p_w != 0.                                        (C1)
```

The least `d` for which there are positive contractions `c_(v,k) in M`
satisfying

```text
(1-sum_(k=1)^d c_(v,k))p_v=0,                        (C2)
[c_(v,k),p_v]=0,                                     (C3)
c_(v,k)c_(w,k)=0                     (v!=w)           (C4)
```

is exactly

```text
chi(G_p).                                            (C5)
```

This obstruction is stable under small errors: if `d<chi(G_p)`, there is
`rho>0` such that every family of positive contractions has at least one
of the three defects in (C2)--(C4) of norm at least `rho`.

In particular, take in `M_2` the rank-one projections onto

```text
(1,0),       (1,1)/sqrt(2),       (1,i)/sqrt(2).
```

Their graph is `K_3`, so two coupled labels do not cover them.  Nevertheless,
for the normalized trace their total support mass is `3/2<=2`; indeed every
subset satisfies the natural span-capacity inequality

```text
sum_(v in S) tau(p_v)
 <=2 tau(join_(v in S) p_v).                         (C6)
```

Hence neither total tracial capacity nor all subset span-capacity
inequalities suffice to construct same-labelled orthogonal cutters.  Even
after tracial capacity is available, a genuinely noncommutative incidence
obstruction remains.

