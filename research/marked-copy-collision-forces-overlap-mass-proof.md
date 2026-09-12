---
rg: 2
id: marked-copy-collision-forces-overlap-mass-proof
kind: route
title: Cauchy-Schwarz against the unit, then substitute the marked density
target: marked-copy-collision-forces-overlap-mass
requires:
  - gram-branching-capacity-with-overlap
  - marked-hs-separation-forces-spectral-density
---

**`(MCC1)`.**  Expanding `S^2` and using `Q_a^2 = Q_a`,

```text
tau(S^2) = sum_a tau(Q_a) + sum_(a != b) tau(Q_a Q_b) = tau(S) + sum_(a != b) tau(Q_a Q_b).
```

Cauchy--Schwarz for the trace state gives
`tau(S)^2 = tau(S . 1)^2 <= tau(S^2) tau(1) = tau(S^2)`.  Combining the two
displays yields `(MCC1)`.  This is exactly `(GBC1)` of
`gram-branching-capacity-with-overlap` specialized to `P=1` (so `x=1` and the
leakage `l` vanishes) with the `T_a` taken to be the inclusions of `Q_a`, whose
sources are the `Q_a` themselves; there `s^2 <= 1 . (s+o)` is `o >= s^2-s`.

**`(MCC2)`.**  The map `u |-> u^2-u` is increasing on `[1/2,inf)`, and
`s >= m beta >= 1 > 1/2`, so `s^2 - s >= (m beta)^2 - m beta`.

**`(MCC3)`.**  `marked-hs-separation-forces-spectral-density` gives
`tau(Q_(1/2)) >= 3 alpha^2/(16-alpha^2)` from `(MSD1)`, which at `alpha^2=2`
equals `6/14 = 3/7`.  With `m=3`, `m beta = 9/7 >= 1` and
`(9/7)^2 - 9/7 = 81/49 - 63/49 = 18/49`.
