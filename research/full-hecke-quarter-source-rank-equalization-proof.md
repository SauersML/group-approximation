---
rg: 2
id: full-hecke-quarter-source-rank-equalization-proof
kind: route
title: Normalize the two full-Hecke sign cuts and insert them into the affine gauge formula
target: full-hecke-quarter-source-equalizes-selector-ranks
requires:
  - b2-b3-pair-full-hecke-four-native-sectors
  - two-shared-gauge-selector-rows-have-an-affine-rank-obstruction
---

By `b2-b3-pair-full-hecke-four-native-sectors`, the four commuting
projections

```text
E_(epsilon,delta)=Q(1+epsilon r)(1+delta t)/4
```

all have rank `rank(Q)/4`.  Summing the two projections with fixed
`epsilon=+1` gives

```text
R_1=E_(+,+)+E_(+,-),
rank(R_1)=rank(Q)/2.
```

Summing with fixed `delta=+1` similarly gives

```text
R_2=E_(+,+)+E_(-,+),
rank(R_2)=rank(Q)/2.
```

Their product is `E_(+,+)`, so its rank is `rank(Q)/4`.  This proves
`(FQE2)`.

For a label reflection of negative fraction `q` and a multiplicity
involution whose positive fraction is `theta`, the affine target fraction
is

```text
Phi_q(theta)=1-q+(2q-1)theta.
```

Substitution of `theta=1/2` gives `Phi_q(1/2)=1/2` independently of `q`.
In particular this holds for `q=1/4` and `q=1/8`, so both full-Hecke source
fractions match their controlled targets with the same balanced gauge.

For an explicit finite-dimensional realization, take an even-dimensional
multiplicity space and a balanced involution `V`.  Both
`C_(1/4) tensor V` and `C_(1/8) tensor V` have equally sized positive and
negative eigenspaces.  On the source take two commuting balanced
reflections whose joint positive sectors all have one quarter of the total
rank.  Each source reflection is unitarily conjugate to its corresponding
controlled target reflection, while the source intersection has rank one
quarter.  Hence the rank and shared-gauge data alone are exactly
consistent.
