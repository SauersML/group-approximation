---
rg: 2
id: fixed-holonomy-on-overlap-pays-relator-energy
kind: claim
title: A fixed finite-factor holonomy on an overlap costs relator energy that multiplicity cannot dilute
artifacts:
  - research/artifacts/pauli-overlap-dichotomy-2026-08-20.md
distinct_from:
  atlas-a4-holonomy-coherence-gap: that is a numerical ceiling on two S3 covariance defects of exact regular A4 context networks; this is an elementary lower bound converting any fixed finite-factor action on a corner into normalized-HS relator energy, with no atlas content.
  constant-block-contraction-gap: that bounds the distance from a block contraction to the constant-block subspace; this bounds the distance of a unitary from the identity given its action on one corner.
  bounded-overlap-syndrome-energy-accounting: that aggregates local charges into a global energy bound; this manufactures a single local charge from a holonomy.
---

Let `(M,tau)` be a finite tracial von Neumann algebra, `R in M` a projection,
and `W in M` a unitary.  Suppose that on the corner `RMR` the element `W`
factorizes as

```text
W|_R  =  A tensor H,
```

where `A` is a **fixed** matrix of some finite size acting on a tensor factor
and `H` is an arbitrary contraction on the complementary multiplicity factor,
with `tr` denoting normalized trace on each factor.  Then

```text
||W - 1||_2^2  >=  2 ( 1 - |tr A| ) tau(R).                          (FHO1)
```

**Commutator form.**  If `X,Y` are unitaries whose restrictions to `R` are
`U tensor H_1` and `V tensor H_2` with the multiplicity factors `H_1,H_2`
commuting, then `[X,Y]|_R = [U,V] tensor H_1H_2` and `(FHO1)` gives

```text
||[X,Y] - 1||_2^2  >=  2 ( 1 - |tr [U,V]| ) tau(R).                  (FHO2)
```

**The S3 instance.**  For two distinct reflections `U,V` in the standard
two-dimensional representation of `S_3`, the commutator `[U,V] = (UV)^2` is
rotation by `240` degrees, so `tr[U,V] = -1/2` and

```text
||[X,Y] - 1||_2^2  >=  tau(R).                                       (FHO3)
```

**Why the multiplicity cannot wash it out.**  The bound is obtained by
minimizing over *all* possible `H`, and the minimum is attained at `|tr H| = 1`.
So an approximator is free to choose the multiplicity behaviour however it likes
and still pays `2(1-|tr A|)` per unit of corner trace.  This is what makes a
holonomy usable as a local charge: unlike a rank or an index, it survives
amplification.

**Composite with the collision bounds.**  If a marked word supplies three
copies of a carrier of trace `3/7` whose pairwise overlaps carry the `S_3`
holonomy above, then `(IGS3)` gives total overlap at least `9/49` and `(FHO3)`
converts it into

```text
sum_(incompatibility relators r) ||r - 1||_2^2 >= 9/49.              (FHO4)
```

That composite is the shape of a non-hyperlinearity certificate.  What it does
**not** supply is a group whose relations actually produce three such carriers
with distinct fixed holonomies on their overlaps; that is
`mixed-relations-force-holonomy-or-transverse-recovery`.
