---
rg: 2
id: strict-iwahori-repair-has-no-uniform-hs-neighborhood
kind: claim
title: Strict Iwahori repair has no dimension-uniform HS neighborhood even within torsion strata
distinct_from:
  sl2-half-explicit-strict-flexible-separation: that gives a macroscopically separated compressed Weil sequence; this puts strict instability inside arbitrarily small neighborhoods of compatible points in the very same torsion stratum.
  iwahori-two-loci-have-zero-uniform-angle: that excludes global strict linear regularity; this excludes every strict local modulus on a dimension-uniform HS tube and every positive-power error bound along a sequence approaching the compatible locus.
  modular-strata-have-linear-coordinates-and-rank-splits: that supplies coordinates of every given endpoint in a stratum; the present obstruction shows that those coordinates do not turn HS proximity into a strict repair estimate.
artifacts:
  - research/artifacts/strict-iwahori-stratum-neighborhood-obstruction-2026-09-08.md
---

Let `Gamma=SL_2(Z[1/2])`, and use the two modular vertices with fixed
generators `s_i,b_i`, where `s_i^2=b_i^3` is the central involution.
Use normalized Hilbert--Schmidt tuple distance in a common dimension `N`.
For an exact vertex pair `phi`, write `D_N(phi)` for distance to all
compatible pairs in dimension `N`, and `D_str(phi)` for distance to the
compatible pairs with the same four generator multiplicity lists as `phi`.
These are **strict** distances, not the generalized flexible distance.

There are constants `c,C>0` and, for every sufficiently large pair of
primes `q>p>3`, exact central-positive vertex pairs `phi_(p,q)` such that,
with

```text
r=12 floor((p-1)/12),   k=p-r in {1,...,12},   N=r+q,
```

one has

```text
def(phi_(p,q)) <= C/sqrt(N),
c sqrt(r/N) <= D_N(phi_(p,q)) <= D_str(phi_(p,q)) <= 2 sqrt(r/N).
```

The same-stratum compatible comparison is explicit: a sum of `r/12`
regular representations of `PSL_2(F_3)=A_4`, together with the
`q`-dimensional projective-line Steinberg representation at prime `q`.

Consequently, for every `epsilon>0`, there is no dimension-independent
function `f(t)->0` such that

```text
D_str(phi) <= epsilon  implies  D_N(phi) <= f(def(phi)).
```

Moreover, along primes `p log p<q<2p log p`, `D_str(phi)->0` but
`D_N(phi)/def(phi)^alpha -> infinity` for every `alpha>0`.
Thus no positive-power strict error bound is rescued merely by requiring
the pair to approach a compatible point in its own stratum.

Adding exactly `k<=12` dimensions supplies an explicit compatible
comparison at generalized distance `O(N^(-1/2))`. This theorem leaves
flexible Iwahori stability, operator-norm neighborhoods, and uniform
infinitesimal rigidity untouched.
