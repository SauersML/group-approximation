---
rg: 2
id: fpbs-box-event-wedge-angle-law-refutes-restriction-proof
kind: route
title: Proof of the one-arm floor, monotonicity and FKG half-split for the wedge family of pinch-wall box events, the restriction-wedge calculus and its incompatibility with the floor, and triangular-lattice measurements of zeta(theta)
target: fpbs-box-event-wedge-angle-law-refutes-restriction
requires:
  - fpbs-cle6-hull-wedge-event-is-not-the-box-event
---

## 0. Setting

Triangular site percolation at `p = 1/2`, notation as in
`fpbs-cle6-hull-wedge-event-is-not-the-box-event`: axial coordinates
`(i,j)`, position `x = i + j/2`, `y = j sqrt(3)/2`; the box `B_n`
(`|j| <= n`, `|x| <= n`) with black (wired) boundary sites; `I_n` the black
cluster of `∂B_n`; `S_n = {(i,0) : -n < i <= 0}`. A step `c -> c + d_k` is a
*pinch* if both common neighbours `c + d_{k±1}` lie in `I_n` or outside
`B_n`.

For `0 <= theta < pi` put

    X_theta = { sites z != 0 with |arg z| < theta }      (X_0 = positive axis),
    X_theta^+ = X_theta ∩ {y >= 0},   X_theta^- = X_theta ∩ {y <= 0}.

So `X_{pi/2} = {x > 0}` is the set `X` of the predecessor, and every
`X_theta` contains the positive axis `R = {(i,0) : i >= 1}`. For a set
`Y` of sites define

* `D'_n(Y)`: no path of non-`I_n` sites without pinch steps joins a site of
  `Y` to a site of `S_n` (pinch-wall proxy);
* `D_n(Y)`: no white circuit in `B_n` surrounds a site of `S_n` and contains
  a site of `Y` (circuit form).

We write `D'_n(theta) = D'_n(X_theta)`, `D_n(theta) = D_n(X_theta)`,
`D'^±_n = D'_n(X_{pi/2}^±)`. The predecessor's `D'_n`, `D_n` are the case
`theta = pi/2`. Its proof of `D'_n ⊆ D_n` (the pinch lemma and (F1)) uses
nothing about `X` except that the flood starts from `X`, so

    (0.1)   D'_n(Y) ⊆ D_n(Y)   for every set Y of sites.

Exponents: `zeta(theta) = lim -log P(D'_n(theta)) / log n` and
`rho = lim -log P(D'^+_n) / log n` when the limits exist; otherwise read
every statement below with `liminf`/`limsup` in the obvious direction.

## 1. Monotonicity

**Lemma 1.** (a) If `Y ⊆ Y'` then `D'_n(Y') ⊆ D'_n(Y)` and
`D_n(Y') ⊆ D_n(Y)`. In particular `theta -> P(D'_n(theta))` is
nonincreasing and `zeta` is nondecreasing.
(b) `D'_n(Y)` and `D_n(Y)` are increasing events (in the black sites).

*Proof.* (a) A witness path (or circuit) for `Y` is one for `Y'`.
(b) Let `omega <= omega'` (more black in `omega'`). Then
`I_n(omega) ⊆ I_n(omega')`, because a black path to `∂B_n` stays black.
So the non-`I_n` sites of `omega'` are non-`I_n` in `omega`. A step that is
a pinch in `omega` has both common neighbours in `I_n(omega) ⊆ I_n(omega')`
or outside `B_n`, so it is a pinch in `omega'`. Hence every admissible path
(non-`I_n` sites, no pinch step) of `omega'` is admissible in `omega`, and a
failure of `D'_n(Y)` in `omega'` is a failure in `omega`. For `D_n`, a white
circuit of `omega'` is white in `omega`. ∎

## 2. The one-arm floor

Let `N[0]` be the origin together with its six neighbours, `N_2[0]` the
19 sites at graph distance `<= 2` from the origin, and `A_n` the event that
some site of `N_2[0]` is joined to `∂B_n` by a black path.

**Lemma 2.** For every `0 <= theta < pi`, and also for `X^±_{pi/2}`,

    D'_n(theta) ⊆ D_n(theta) ⊆ A_n,     hence
    P(D'_n(theta)) <= P(A_n) <= C n^{-5/48 + o(1)},   zeta(theta) >= 5/48,
    and likewise rho >= 5/48.

*Proof.* The first inclusion is (0.1). Suppose `A_n` fails. Let `U` be
`N[0]` together with every black cluster (inside `B_n`) that meets
`N_2[0]`. `U` is connected, since every site of `N_2[0]` is adjacent to
`N[0]`. Since `A_n` fails, no site of `U` is black and joined to
`∂B_n`. In particular `U` contains no boundary site and no site adjacent
to one: boundary sites are black and would join `U` to `∂B_n`. Let `F` be the fill of `U` (U plus the bounded components of its
complement) and `C` the outer boundary of `F`: the sites outside `F`
adjacent to `F`. On the triangular lattice `C` is a circuit surrounding
`F`, and it lies in `B_n` because `F` avoids `∂B_n` and its neighbours in
the exterior region are sites of `B_n`.

Every site `c` of `C` is white. Indeed `c` is adjacent to a site `u ∈ U`
(a neighbour in `F \ U` would be enclosed, hence not outer). If `u` is
black, `u` lies in a black cluster of `U` and a black `c` would lie in the
same cluster, so in `U`. If `u` is white, then `u ∈ N[0]`, so `c ∈ N_2[0]`, and a
black `c` would have its black cluster in `U`. Either way `c ∉ U`
forces `c` white.

So `C` is a white circuit in `B_n` surrounding the origin `(0,0) ∈ S_n`.
Walk along row 0 from `(1,0) ∈ N[0] ⊆ F` towards `(n,0) ∈ ∂B_n ∉ F`. The
first site `(i,0)` not in `F` is adjacent to its predecessor in `F`, so it
lies in `C`, with `i >= 2`. It therefore lies in `R ⊆ X_theta`, and also
in `X^±_{pi/2}`. Hence `D_n(theta)` fails. The bound
on `P(A_n)` is the whole-plane one-arm exponent `5/48`
(Lawler-Schramm-Werner, Smirnov) with a union bound over the 19 sites of
`N_2[0]`. ∎

Lemma 2 is elementary, but it is the rigid constraint used in §4: the
exponent of the box event can never fall below `5/48`, whatever the target
angle, because a white circuit around the origin always reaches the
positive axis.

## 3. The FKG half-split

**Lemma 3.** `D'_n = D'^+_n ∩ D'^-_n` and

    P(D'_n) >= P(D'^+_n) P(D'^-_n) = P(D'^+_n)^2,   so   zeta(pi/2) <= 2 rho.

*Proof.* `X_{pi/2} = X^+ ∪ X^-`. An admissible path from `X` to `S_n` starts
in `X^+` or in `X^-`, so `D'_n` fails iff `D'^+_n` or `D'^-_n` fails. Both
are increasing (Lemma 1(b)), so Harris-FKG gives the product bound. The map
`(i,j) -> (i+j, -j)` is a lattice automorphism fixing `x` and sending `y` to
`-y`. It preserves `B_n`, `∂B_n`, `S_n`, the colouring law, `I_n`, pinches,
and swaps `X^+` with `X^-`, so `P(D'^+_n) = P(D'^-_n)`. ∎

**Corollary 3.1.** Suppose `P(D'^+_n) >= c n^{-rho'}` with `rho' < 3/16`.
Then `P(D_n) >= P(D'_n) >= c^2 n^{-2 rho'}`, and `2 rho' < 3/8`, which is
the triangular form of (H) in
`fpbs-geodesic-bisector-chain-polynomial-in-inverse-theta`.

So the gate reduces rigorously to a one-quadrant event: no pinch-free
non-`I_n` path from the closed-below quadrant `{x > 0, y >= 0}` to the
negative axis. The floor gives `rho >= 5/48`, so the reduction can only
work if `rho` lies in `[5/48, 3/16)`.

*Remark 3.2 (the half-split loses).* §5 measures `rho = 0.211(7)`, which
is outside the window, while `zeta(pi/2) = 0.256 < 2 rho ≈ 0.42`. The events
`D'^+_n` and `D'^-_n` are strongly positively correlated: both are driven
by the same wired cluster sealing off the neighbourhood of the origin.
Corollary 3.1 is a correct reduction, but its hypothesis is numerically false, so it fails as a
route. Any proof of (H) must keep the two halves together.
## 4. The restriction-wedge calculus and why the floor breaks it

The step proposed for this node was: explore from the wired boundary along
`S_n` with a one-sided SLE_6 exploration, cut it at CLE_6 pinches, and bound
`P(D'_n)` below by a restriction (SLE_{8/3}-type) wedge exponent. Any such
bound has the following form, which we call **(M1)**. Open the slit with
`w = sqrt(z)` (branch cut along `S_n`). The slit domain `B_n \ S_n` becomes
a half-disc of radius `~ sqrt n` over the imaginary axis. The two banks of
`S_n` become the imaginary axis, and `X_theta` becomes the wedge
`W_theta = {|arg w| < theta/2}`. (M1) is the ansatz that the event costs what a one-sided restriction
sample of exponent `alpha`, attached to the imaginary axis, pays to avoid
`W_theta` up to radius `sqrt n`, with the exponent carried by the covariant
wedge factor of the slit picture: the angular size `pi + theta` of the
target side (both banks and the wedge) over the free opening
`pi - theta`. This is the heuristic that gives the proposed step its
numbers. (M1) predicts

    (4.1)   zeta_M1(theta) = alpha (pi + theta) / (pi - theta),

so `zeta_M1(0) = alpha` and `zeta_M1(pi/2) = 3 alpha`. The ratios
`zeta(theta)/zeta(pi/2)` are `1/3, 5/9, 1, 7/3` at `theta = 0, 45, 90,
135` degrees. Within the ansatz, the rational factor comes from conformal covariance of the
one-sided restriction law: the exponent of a restriction sample in a wedge
of opening `beta` is `alpha·pi/beta`. The only free parameter is `alpha`.

**Proposition 4.1 (the floor fixes the window).** If (M1) holds with some
`alpha`, then Lemma 2 at `theta = 0` gives `alpha >= 5/48`, hence

    zeta(pi/2) = 3 alpha >= 5/16 = 0.3125.

The gate `zeta(pi/2) < 3/8` needs `alpha < 1/8`. So an (M1)-type proof can
only succeed with `alpha ∈ [5/48, 1/8)`, and then it predicts
`zeta(pi/2) ∈ [0.3125, 0.375)`.

*Proof.* Immediate from (4.1), Lemma 2 and Lemma 1(a). ∎

**The window excludes the proposed laws.**

* SLE_{8/3}: `alpha = 5/8` gives `zeta(pi/2) = 15/8`.
* The SLE_6 hull (the locality/restriction exponent `1/3` of the one-sided
  exploration): `zeta(pi/2) = 1`.

Both exceed `3/8` by a wide margin, and this matches the w16 measurement of
the hull events `H_n` (slopes `1.1`–`2`). The one-sided restriction laws
with `alpha < 5/8` are SLE(8/3; rho), with
`alpha(rho) = (rho + 2)(3 rho + 10)/32`. The window `[5/48, 1/8)` means
`rho ∈ [rho_*, -4/3)` with `rho_* ≈ -1.42`, i.e. boundary-touching curves
tuned to one specific force point. Nothing in the percolation exploration
selects such a `rho`.

**(M1) is inconsistent with the box event itself.** Proposition 4.1 makes a
testable prediction: `zeta(pi/2) >= 5/16` and `zeta(0)/zeta(pi/2) = 1/3`.
The measurements in §5 give `zeta(pi/2) = 0.256(6)` on the triangular
lattice (the Z^2 circuit form gave `0.251(6)`), which is below `5/16`. They
also give `zeta(0)/zeta(pi/2) = 0.58(2)`, not `1/3`. So no single
restriction exponent in the slit picture governs the box event: the floor
and the data rule out every `alpha` at once. The quantitative form of this
is the mechanism test in §6.2.

For comparison, plain conformal covariance of `D'_n(theta)` in the
*unslit* plane, **(M2)**, treats the negative axis as the boundary arc of
a wedge of opening `pi - theta` (the complement of `X_theta`). It predicts

    (4.2)   zeta_M2(theta) = zeta(0) · pi / (pi - theta),

with ratio `zeta(0)/zeta(pi/2) = 1/2`. The measured `0.58(2)` misses this
too, by about four standard errors. The event is not a
single-exponent covariant wedge event at these sizes, in either picture.

## 5. Measurements

`experiments/fpbs-pinch-wedge-angle-2026-09-18/tri_wedge.c` is the w16
flood `tri_d.c` with the source set replaced by `X_theta` (optionally
intersected with `{y >= 0}`). It samples `N = 256` boxes and records
`D'_n` for `n = 8, ..., 256` in one nested sample. Each run was capped at
1100 s. The slope is `-log2 P(D'_{2n})/P(D'_n)`, and the pooled value is
`log2(P(D'_16)/P(D'_256))/4`. Errors are from a 20-block jackknife
(`pool.py`; full tables in `results.txt`).

| event | samples | local slopes, n = 16..256 | pooled | `P(D'_256)` |
|---|---|---|---|---|
| `D'_n(0)` (positive axis) | 6000 | .139 .155 .151 .146 .144 | 0.149(4) | 0.399 |
| `D'_n(pi/2)` (`x > 0`) | 6000 | .273 .258 .232 .276 .258 | 0.256(6) | 0.197 |
| `D'_n(X^+)` (quadrant) | 6000 | .208 .200 .209 .227 .209 | 0.211(7) | 0.268 |
| `0 ∈ I_n` (one-arm check) | 6000 | .091 .104 .107 .101 .096 | — | 0.319 |

The one-arm column reproduces `5/48 ≈ 0.104`, and every monotonicity check
passes (0 violations). The w16 run (3000 samples, `n <= 512`) gave
`0.27(2)` for `D'_n(pi/2)`, consistent with `0.256(6)`.

Readings:

* `zeta(0) = 0.149(4) > 5/48`. So the floor of Lemma 2 is not attained.
* `zeta(0)/zeta(pi/2) = 0.58(2)`. (M1) predicts `1/3` (excluded) and (M2)
  predicts `1/2` (off by about four standard errors).
* (M1) with `alpha = zeta(0)` predicts `zeta(pi/2) = 0.447(12)`. That is
  above the gate and far from the measured value.
* `rho = 0.211(7) > 3/16`: the half-split of Corollary 3.1 fails
  (Remark 3.2). Also `zeta(pi/2) < 2 rho`, and in fact
  `zeta(pi/2) < 2 zeta(0) = 0.298(8)`.

## 6. Consequences for (H)

1. **Rigorous.** For every target wedge, the box event costs at least the
   one-arm exponent (Lemma 2). So the gate `zeta(pi/2) < 3/8` has a
   rigorous window `[5/48, 3/8)`, and it follows from the quadrant bound
   `rho < 3/16` (Corollary 3.1).
2. **Mechanism test.** A slit-picture restriction bound ties the exponents
   at different angles by (4.1). The angle law measured here excludes
   (4.1) by a wide margin. Such a bound would certify an exponent
   `3 zeta(0) ≈ 0.45`, which is above `3/8`. So the route proposed for this
   step (SLE_6 exploration along `S_n`, closed at pinches, compared with
   an SLE_{8/3}/restriction wedge) cannot prove (H), whatever `alpha` it
   produces. Applied at `theta = 0`, such a bound reads
   `P(D'_n(0)) >= n^{-alpha}`, so `alpha >= zeta(0)`. That is
   rigorously `>= 5/48` and numerically `>= 0.149`. At `theta = pi/2`
   it then certifies only `n^{-3 alpha}`, where `3 alpha >= 5/16`
   rigorously and `>= 0.447 > 3/8` numerically.
3. **Decorrelation test.** `rho ≈ 0.21` exceeds `3/16`, so the FKG
   half-split cannot close the gate either. The two halves share the
   sealing wired cluster, and a proof must handle them jointly.
4. **What survives.** Neither covariance law fits. The data satisfy
   `zeta(pi/2) = 0.256(6) < 2 zeta(0) = 0.298(8)`. So (H) would follow
   from two statements:

   - the widening inequality `P(D'_n(pi/2)) >= c P(D'_n(0))^2`: widening
     the target from the positive axis to the half-plane costs no more
     than a second independent copy of the axis event;
   - `zeta(0) < 3/16` for the axis-to-axis event, measured at
     `0.149(4)`.

   The event `D'_n(0)` has no bulk target: it asks that the wired cluster
   separate the two half-axes through pinches. That makes it a
   two-boundary-arc event, the natural object for an exact
   external-perimeter computation in the unslit plane.
