---
rg: 2
id: bs14-exact-variety-hs-local-rigidity-proof
kind: route
title: Multiscale clustering, HS Davis-Kahan, and monodromy transport
target: bs14-exact-representation-variety-is-hs-locally-rigid
requires: []
---

**Classification.**  An exact pair `(V, W)` decomposes as a direct
sum of irreducibles `(C, omega)`: `C` an `x4`-cycle of odd roots of
unity of length `l`, `omega` a monodromy phase; `V` acts on the cycle
lines by the cycle roots, `W` shifts along the cycle with `W^l`
returning `omega`.  Multiplicities are constant along each cycle.

**Step 1 (equivariant multiscale clustering).**  The `x4`-map acts on
the odd spectral positions; cluster positions `x4`-equivariantly at a
scale `s` chosen by pigeonhole over dyadic scales in
`[eps^(1/2), eps^(1/4)]` so that the spectral mass of `V` and `V'`
within distance `s^2`-bands of cluster boundaries is at most
`eps^(1/2)` — the standard scale-selection argument, whose constants
count dyadic scales only and are dimension-free.  Discard the
boundary mass into the error budget.

**Step 2 (HS Davis--Kahan).**  For each cluster `j`, the spectral
projections satisfy `||P_j - P'_j||_2 <= C ||V - V'||_2 / gap <= C
eps / s^2`-aggregated; summing in Hilbert--Schmidt over clusters
(orthogonal ranges) keeps the total at `C eps / s^2` in normalized
HS.  A polar rotation `u_0` carries the `P'`-system onto the
`P`-system at that cost, `x4`-equivariantly since the clustering is.

**Step 3 (cluster-local data and transport).**  After `u_0`, both
representations share cluster projections.  Within the cluster system
the remaining invariants are, per `x4`-orbit of clusters: the
multiplicity (equal for both up to the discarded mass, since ranks of
close projections agree after discarding), and the CLUSTER MONODROMY
— the polar spectrum of `P_j W^l P_j` — which is an HS-continuous
functional of the pair at scale `s`: the two monodromy spectra are
within `C(eps + eps/s^2)` in transport.  Now build the conjugacy
directly on the classification: within each cluster orbit, both
representations are direct sums of irreducibles whose positions lie
within `s` of the cluster center and whose monodromies are within the
computed transport of each other; matching them pairwise (positions
within `2s`, monodromy phases by their transport plan) defines a
unitary intertwiner up to errors `2s` in `V` and the monodromy
transport in `W`.  Cross-length reorganizations inside a cluster
(different odd orders and cycle lengths colliding) are exactly the
discontinuities of the invariant multiset, but any two organizations
of the same cluster-local data differ by unitaries moving `V` by at
most the cluster diameter and `W` by at most the monodromy transport
— the representation distance never sees the discontinuity.

**Total.**  `f(eps) <= C (s + eps/s^2 + eps^(1/2))`; with
`s = eps^(1/3)` all terms are `O(eps^(1/3))`, dimension-free.  (The
exponent is not optimized.)  Every constant counts scales or uses
orthogonality; nothing counts dimension or cycle number.  The same
argument with the joint solenoid spectrum of the commuting tower
`{V(x)}` in place of the circle gives the solenoid-group version; the
only new ingredient is that clusters live on the solenoid, and Step 1
clusters finitely many tower levels at once with the same pigeonhole.
