---
rg: 2
id: bounded-profile-puts-short-essential-loops-at-cone-points
kind: claim
title: A permutation pair of rectangle profile K has a homotopically nontrivial closed curve of length O(K) within distance O(K) of every cone point of its square-tiled surface, so the profile is quadratic up to the local systole
distinct_from:
  z2-bounded-rectangle-profile-forces-near-commuting: that is the open statement, bounded profile implies bounded distance. This proves a necessary geometric consequence of bounded profile for permutation pairs, namely short essential loops at every cone point. It is the localisation half of the proposed one-row step, and it does not decide the statement.
  one-row-profile-pairs-need-arc-tori-not-rotations: that bounds the profile by breaks (Lambda <= sup |B_t|) and reformulates distance as arc-tori. This goes the other way, from profile to geometry, for all permutation pairs. It uses CAT(0) geometry of the square-tiled surface, which that node does not use.
  slit-origami-z2-pair-has-rank-distance-half-l: that computes the profile and distance of one family. Corollary 3 here explains why every such family has quadratic profile up to the injectivity scale at its cone points.
  near-exact-tuples-saturate-linear-conversion-defect: that proves distance delta implies profile at most 2 delta. Combined with Corollary 3 here, a pair within distance delta has local systole O(delta) at every cone point.
artifacts:
  - research/bounded-profile-puts-short-essential-loops-at-cone-points-proof.md
  - experiments/one-row-tori-2026-09-19/summary.txt
  - experiments/one-row-tori-2026-09-19/lib.py
  - experiments/one-row-tori-2026-09-19/rankprof.py
  - experiments/one-row-tori-2026-09-19/swap.py
  - experiments/one-row-tori-2026-09-19/chain2.c
  - experiments/one-row-tori-2026-09-19/mkin.py
  - experiments/one-row-tori-2026-09-19/t157.py
  - experiments/one-row-tori-2026-09-19/texc.py
  - experiments/one-row-tori-2026-09-19/exh.py
  - experiments/one-row-tori-2026-09-19/excrep.py
  - experiments/one-row-tori-2026-09-19/rep3.py
  - experiments/one-row-tori-2026-09-19/ratio.awk
  - experiments/one-row-tori-2026-09-19/maxcost.awk
  - experiments/one-row-tori-2026-09-19/rep3_40.txt
  - experiments/one-row-tori-2026-09-19/rep3_60.txt
  - experiments/one-row-tori-2026-09-19/scanC.py
  - experiments/one-row-tori-2026-09-19/scanC200.txt
  - experiments/one-row-tori-2026-09-19/scanC400.txt
  - experiments/one-row-tori-2026-09-19/fails_lib.py
  - experiments/one-row-tori-2026-09-19/failexc.py
  - experiments/one-row-tori-2026-09-19/truelam.py
  - experiments/one-row-tori-2026-09-19/hard200.txt
---

**ESTABLISHED (unreviewed)** (`bounded-profile-puts-short-essential-loops-at-cone-points-proof`). The computation
section below is evidence only and is not part of the established statement.

**Setting.** Let `b` and `c` be permutations of a finite set `X`. Let `S(b, c)` be the square-tiled translation surface
with one square `Q_x` for each `x`, where `Q_x` has right neighbour `Q_(b x)` and top neighbour `Q_(c x)`.
- Its vertices correspond to the cycles of `c^-1 b^-1 c b`, and a cycle of length `m` has cone angle `2 pi m`. A vertex
  is a *cone point* if `m >= 2`.
- The *period* of a closed curve is the translation vector that it develops to.
- For a one-row pair (`b = +1` on `Z/n`), the cone points are exactly the upper-right corners of the squares in the
  break set `B_1` of `c`.

**Statement.** Let `K >= 0` and `R = floor(4K) + 1`, and suppose `rank([b^R, c^R] - I) <= 2 K R`. This holds whenever
`Lambda_rect(b, c) <= K`. Let `v` be a cone point of `S(b, c)`, and let `x` be a square whose upper-right corner is
`v`. Then there are `0 <= i, j < R` such that one of the following holds.
- (a) *Zero-period loop.* `y = c^-j b^-i x` is fixed by `c^-R b^-R c^R b^R`, and the lattice rectangle loop of side `R`
  at `Q_y` is homotopically nontrivial. Its period is `0`.
- (b) *Short nonzero-period loop.* `c^-j b^-i x = c^-j' b^-i' x` for some other `(i', j')` in `[0, R)^2`. This gives a
  closed lattice curve through `Q_x` of length at most `4(R - 1)` with period `(i' - i, j' - j) != 0`.

In both cases the curve lies within distance `4R` of `v`.

**Corollary 3 (quadratic profile below the local systole).** Suppose every closed curve of length at most `4R` in the
ball `B(v, 4R)` is null-homotopic. Then `rank([b^R, c^R] - I) >= R^2 / 2`, and so `Lambda_rect(b, c) >= R / 4`.

**Mechanism.** Lift to the universal cover. It is CAT(0), because every cone angle is at least `2 pi`. A null-homotopic
rectangle loop through square centres is a geodesic quadrilateral with four right angles. By the Flat Quadrilateral
Theorem it bounds a flat rectangle, and a flat rectangle has no cone point inside it. The profile bound says that fewer
than `R^2` of the `R^2` squares near `v` are moved by the commutator.

**What this does for the one-row step.** In the one-row case, every square of `B_1` is within lattice distance `O(K)`,
in the `b` and `c` directions, of a short essential curve. So the candidate cuts of the proposed `(F(K), F(K))`-arc-torus
lie in `U_{|i|, |j| <= O(K)} b^i c^j (B_1)`, as the step requires. The `b`-fattening cannot be dropped.
- The remaining, open half is **surgery**: a short essential curve at every cone point should give a repair of cost
  `O(K)`.
- In genus 2, Gauss-Bonnet shows the following. A simple zero-period closed geodesic in the stratum H(1,1) is a pair of
  parallel saddle connections from `p` to `q` with equal holonomy. Regluing across the pair splits both `4 pi` points and
  leaves one or two tori, at cost about the holonomy length. In the stratum H(2), such a geodesic must pass through the
  cone point twice, which is the closed-pair swap found in the 157 example.
- Not covered:
  - case (b), where tall or thin cylinders need padding (see `E(a, k)` below);
  - polygonal or non-simple zero-period loops;
  - replacing straight slits by lattice staircases with the same move word.

**Computation (evidence, one-row 3-arc exchanges; see `summary.txt`).** `c = arcx(n, theta, alpha, beta, gamma)`
translates `[0, alpha)` by `theta`, the next `beta` points by `theta + gamma`, and the last `gamma` points by
`theta - beta`. A repair is one of the following:
- one slit-pair swap from a cone point, in which two lattice paths with the same move word are swapped (`chain2.c`,
  cost is the larger of the rank changes of `b` and `c`);
- one excision padding, in which `c` is the first return of a rotation of `Z/(n+m)` to the complement of an `m`-arc
  (cost at most `2m + 2`);
- one rotation (cost equal to the number of disagreements).

Findings:
- **157 example, corrected.** `(400, 157, 229, 75, 96)` is repaired by one swap of length 7, at distance at most 4.
  Its moved-based profile is about 9.9. The earlier estimate of about 60 (two thin arc-tori) was far off.
- **Exhaustive, all classes with moved-profile at most 2.5 at `n = 40` and at most 3 at `n = 60, 100`.** Every class is repaired by one swap
  or one excision (two classes at `n = 100` need swap length 9). The maximum cost is 6 at `n = 40` and `n = 100`, and
  8 at `n = 60` (one excision with `m = 3`). It does not grow with `n`. The largest ratio of cost to profile is 3.
- **Random classes at `n = 200` (250 classes) and `n = 400` (108 classes).**
  - At `n = 200`, 233 classes are repaired by one swap of length at most 13, at cost at most `1.89 Lambda^`, and 4 more
    by a rotation. Of the 13 left over, none has an excision with `m <= 30`. The one with the smallest profile,
    `(93, 120, 1, 79)` with `Lambda = 4.94`, is repaired by one swap of length 15 at cost 10. The other 12 are open, with
    `Lambda` between 5.46 and 9.3. In particular `(116, 170, 29, 1)` and `(31, 32, 66, 102)`, both with `Lambda` about
    5.5, have no single swap of length at most 16 (`hard200.txt`).
  - At `n = 400`, the failures are all at `Lambda^ >= 9`, which is near the generic value `sqrt(n)/2 = 10`, where the
    search length 13 is too short.
- **Padding is necessary.** `E(a, k)` has bounded profile while its best swap grows with `a`. Excision with `m = k`
  repairs it. So the target must be the padded arc-torus, not a swap alone.

**Next step.** Prove the surgery half in genus 2. A simple zero-period essential curve of length `L` near each cone
point should give a staircase slit-pair swap of cost `O(L)`. Case (b) should give a padded cylinder cut of cost `O(L)`.
Settle the smallest open classes, `(200, 116, 170, 29, 1)` and `(200, 31, 32, 66, 102)` with `Lambda` about 5.5, by a
repair of cost `O(Lambda)` or by a distance lower bound, using a donor or two-swap search. Then reduce the doubly-wide case to one-row pairs, using the first-return map to a row.
