---
rg: 2
id: raw-swap-forces-two-s3-covariance-energy-proof
kind: route
title: Telescope the twelve H replacements and use weighted Cauchy target: raw-swap-forces-two-s3-covariance-energy
requires: []
---

The exact finite-group audit in `experiments/atlas_raw_reynolds_gap_audit.py`
checks three purely finite facts after the certified inner alignment:

1. all twelve second-chart syllables of the scalarized raw word lie in the
   same subgroup `H`;
2. only two letters `a_0,b_0` occur, with multiplicities `4` and `8`; and
3. replacing every second-chart `H` syllable by its first-chart copy makes
   the folded word exactly the identity.

Write

```text
A = U rho(a_0) U^*,   A_0=rho(a_0),
B = U rho(b_0) U^*,   B_0=rho(b_0).
```

Replace the twelve second-chart syllables one at a time.  All surrounding
factors are unitary, so normalized Hilbert--Schmidt norm is unchanged by the
left and right factors in each telescoping difference.  Four replacements
cost `||A-A_0||_2=a`, eight cost `||B-B_0||_2=b`.  The already-fixed chart and
word identifications contribute the finite packet error `eta`.  Therefore

```text
||raw(U)-1||_2 <= 4a+8b+eta.                           (1)
```

For a separating hyperlinear microstate the raw source word is nontrivial and
has regular character asymptotics, so

```text
||raw(U)-1||_2 -> sqrt(2),
```

while `eta->0`.  Hence

```text
sqrt(2) <= 4a+8b+o(1).                                 (2)
```

Weighted Cauchy--Schwarz gives

```text
(4a+8b)^2 <= (4^2+8^2)(a^2+b^2)=80(a^2+b^2).
```

Squaring `(2)` and dividing by `80` yields

```text
a^2+b^2 >= 2/80-o(1)=1/40-o(1).
```

The same finite audit verifies that `a_0,b_0` are involutions and their
product has order three, so they generate `H~=S_3`.  No compactness,
coordinate-selected commutant element, or unproved representation-theoretic
input is used.
