---
rg: 2
id: marked-copy-collision-forces-overlap-mass
kind: claim
title: Three copies of a marked spectral carrier already have forced pairwise overlap mass
artifacts:
  - research/artifacts/fractional-branch-pressure-2026-08-19.md
distinct_from:
  marked-hs-separation-forces-spectral-density: that produces one positive-density carrier from marked separation; this is the pigeonhole consequence once several copies of such a carrier exist and their total trace exceeds one.
  bounded-overlap-syndrome-energy-accounting: that converts local syndrome charges with bounded overlap into a global energy bound, assuming the charges are given; this forces overlap to exist in the first place and gives an explicit constant.
  common-range-isometries-have-maximal-gram-overlap: that concerns two partial isometries with a common range; this concerns any finite family of projections whose traces sum above one and uses no isometries.
---

Let `(M,tau)` be a finite tracial von Neumann algebra and let `Q_1,...,Q_m` be
projections.  Put `S = sum_a Q_a` and `s = tau(S) = sum_a tau(Q_a)`.  Then

```text
sum_(a != b) tau(Q_a Q_b) = tau(S^2) - tau(S) >= s^2 - s.            (MCC1)
```

In particular if `tau(Q_a) >= beta` for every `a` and `m beta >= 1`, then

```text
sum_(a != b) tau(Q_a Q_b) >= (m beta)^2 - m beta > 0.                (MCC2)
```

**Marked instance.**  By `marked-hs-separation-forces-spectral-density`, a word
`W` with `||W-1||_2 >= alpha` has `tau(Q_(1/2)) >= 3 alpha^2/(16-alpha^2)`; at
the regular-character scale `alpha^2 = 2` this is `3/7`.  With `m=3` copies,

```text
sum_(a != b) tau(Q_a Q_b) >= (9/7)^2 - 9/7 = 18/49.                   (MCC3)
```

Over a third of the normalized trace is forced into ordered pairwise overlap by
three copies alone.

## What this does and does not remove

It removes the need for *expansion* in the syndrome half of
`extensive-cosystolic-index-defect`.  That target asks a construction to
produce `Theta(d)` local carriers; `(MCC2)` shows that a mere three copies of a
positive-density marked carrier already force a fixed positive collision mass,
so the load-bearing content of that target is entirely the conversion of
collision mass into relator energy, not the manufacture of many carriers.

It does **not** by itself give an obstruction, and the reason is
`supercritical-network-needs-noncanonical-cuts`: `(MCC1)` is a universal
projection identity, valid in the group von Neumann algebra of the presented
group, where the collision mass exists and pays nothing.  A usable version must
make the copies *incompatible* through matrix-coordinate data, so that their
collision charges relator energy.  Any argument that derives the payment from a
universal identity is refuting the existence of the group and is wrong.

`(MCC1)` is the case `P=1`, `T_a` the inclusions of `Q_a`, of `(GBC1)` in
`gram-branching-capacity-with-overlap`; it is recorded separately because the
marked-copy reading is a different use of the same inequality.
