---
rg: 2
id: full-hecke-quarter-source-does-not-lock-moving-gauges
kind: claim
title: Full-Hecke four-sector support does not lock the order-seven moving gauges
artifacts:
  - research/full-hecke-quarter-moving-gauge-fence-proof.md
invalidates:
  - full-hecke-quarter-source-locks-moving-gauges
distinct_from:
  b2-b3-pair-full-hecke-four-native-sectors: that proves the sharp four-sector ranks in every exact representation of the actual packet; this shows that those ranks, even on a common quarter source, do not by themselves synchronize a separately typed moving reservoir.
  order-seven-moving-cuts-realize-both-affine-profiles: that gives the two drifting affine profiles separately; this installs both profiles over one literal four-sector Hecke source and keeps its common plus-plus sector positive.
  el20-six-moving-coefficient-square-bridges: that asks for actual ordinary EL20 words mixing the two interfaces; this is a scoped counterpacket to omitting that mixed occurrence input.
---

**ESTABLISHED EXACT QUARTER-SOURCE FENCE.**  The full-Hecke sign geometry
and the order-seven moving-cut rows have an exact joint finite model in
which the common native source is positive but the reservoir gauges remain
unlocked.

More precisely, there are a projection `Q`, commuting involutions `r,t`
on `QH`, and involutions `B_2,B_3` reducing `Q` such that

```text
B_2rB_2=-r,       [B_2,t]=1,
B_3tB_3=-t,       [B_3,r]=1.                         (HQF1)
```

Consequently the four projections

```text
E_(epsilon,delta)=Q(1+epsilon r)(1+delta t)/4
```

all have rank `rank(Q)/4`.  In particular

```text
F=Q(1+r)(1+t)/4,              rank(F)=rank(Q)/4.     (HQF2)
```

On the same finite space there are two exact seven-stage moving systems.
Their initial multiplicity involutions `D_1,D_2` have positive spectral
fractions

```text
theta(D_1)=1/2,                    theta(D_2)=5/6,    (HQF3)
```

and their stage copies `D_(i,k)` obey

```text
product_(k=0)^6 D_(i,k)=1,       D_(i,k+1)!=D_(i,k)  (HQF4)
```

for some `k`.  Hence both order-seven heads have exact seventh power one
and zero moving boundary.  The two controlled output rows with label
fractions `1/4` and `1/8` have source negative fractions `1/2` and `1/4`,
respectively, exactly as in the affine selector endpoint.  Restricting the
moving systems to the common quarter sector `F` changes none of the
reservoir data.

Taking the native head itself as the parallel bridge makes every displayed
mixed square exact, but tautological.  The nonconstant stage gauges and the
inequality of `(HQF3)` persist.  Therefore the conclusions of
`b2-b3-pair-full-hecke-four-native-sectors`, even combined with exact
order-seven moving rows and the two affine rank profiles, do not imply the
ungauged fixed-Hecke-frame typing `(ESB2)`.

The claim is deliberately scoped.  It is not a representation of the full
EL20 coefficient presentation and does not refute a new ordinary mixed
coefficient word.  It proves that the newly paid B2/B3 quarter source is a
mass input only: the remaining EL20 bridge must contain a relation which
mixes that sign packet with the moving reservoir occurrence.  Separate
support and seventh-power tables cannot supply it.

No Property T, Kazhdan input, canonical trace, computation, literature
theorem, or Lean compilation is used.

DERIVATION
full-hecke-quarter-moving-gauge-fence-proof
