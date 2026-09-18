---
rg: 2
id: sl2-z-inverse-pq-is-not-strictly-hs-stable
kind: claim
title: SL2(Z[1/pq]) is not Hilbert--Schmidt stable in the same-dimension sense
distinct_from:
  sl2-half-explicit-strict-flexible-separation: that separates strict from flexible repair for PSL_2(Z[1/2]) with the even Weil packet; this refutes strict stability for the three-place lattices SL_2(Z[1/pq]) with Steinberg packets, whose (T;FD) comes from the co-dense subgroup rather than from the lattice directly.
  infinite-hyperlinear-kazhdan-group-is-not-hs-stable: SL_2(Z[1/pq]) does not have property (T) (it surjects onto an amalgam action on the Bruhat--Tits tree of SL_2(Q_q) without fixed points), so that theorem does not apply; this uses only (T;FD).
  sl2-z-inverse-pq-is-hs-stable: that is the positive strict-stability claim; this is its refutation.
---

Let `p != q` be primes and `G = SL_2(Z[1/pq])`.  Then `G` is **not**
HS-stable in the same-dimension sense of `sl2-z-inverse-pq-is-hs-stable`.
There are `eps > 0` and, for every prime `l` not dividing `pq`, a unitary
tuple `tau_l` of dimension `l - 1` on a fixed finite generating set.  The
relator defect of `tau_l` is `O(l^(-1/2))`.  Every exact representation of
`G` in `U(l - 1)` is at distance `>= eps` from `tau_l` on generators.

`tau_l` is the polar compression of the Steinberg representation of
`SL_2(F_l)`, pulled back along reduction mod `l`, to the orthocomplement of
one unit vector.

**Consequence for the routes.**
- Every route that consumes `sl2-z-inverse-pq-is-hs-stable` in the strict
  reading is dead.  This covers `codense-kazhdan-host-from-sl2-pq-stability`
  and the Pauli lamplighter instance in
  `sl2-s-arithmetic-pair-is-codense-kazhdan`.
- The consumers that only need flexible stability are untouched: the
  Corollary of `hnn-over-codense-kazhdan-subgroup-not-hyperlinear`, which
  asks for flexible stability by Dogon--Vigdorovich Definition 1.2.
- The surviving hole is flexible HS stability of `SL_2(Z[1/pq])`.  By this
  claim, a proof of that would also settle
  `flexibly-but-not-strictly-hs-stable-group-exists`.
