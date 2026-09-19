---
rg: 2
id: fpbs-cle6-hull-wedge-event-is-not-the-box-event
kind: claim
title: The CLE_6 wedge event proposed for the FPBS critical inequality (H) is the hull form of the box event, a strict sub-event of the circuit form D_n; on the triangular lattice it forces a black half-plane arm (so P <= C n^{-1/3+o(1)}), numerically decays faster than n^{-1} while D_n decays like n^{-0.27}, and the continuum object for zeta is filled-cluster (external-perimeter) boundaries, not CLE_6 loops
distinct_from:
  fpbs-geodesic-bisector-chain-polynomial-in-inverse-theta: that reduces the gate to (H), P_{1/2}(D_n) >= pi(n)^beta with beta < 18/5 (zeta < 3/8 on the triangular lattice), and proposes (§3.4) to compute zeta from a CLE_6 loop event; this shows that loop event is a different, much rarer event, so the proposal does not give (H), and names the correct target
artifacts:
  - research/fpbs-cle6-hull-wedge-event-is-not-the-box-event-proof.md
  - experiments/fpbs-cle6-wedge-exponent-2026-09-18/tri_d.c
  - experiments/fpbs-cle6-wedge-exponent-2026-09-18/pool.py
  - experiments/fpbs-cle6-wedge-exponent-2026-09-18/run_all.sh
  - experiments/fpbs-cle6-wedge-exponent-2026-09-18/results.txt
---

**Status.** Theorem 1 (a)-(c) are ESTABLISHED (proof in
`fpbs-cle6-hull-wedge-event-is-not-the-box-event-proof`). The exponent
values are NUMERICAL. (H) itself stays OPEN.

**Context.** `fpbs-geodesic-bisector-chain-polynomial-in-inverse-theta`
reduced the FPBS bisector gate to

    (H)   P_{1/2}(D_n) >= c pi(n)^beta   for some beta < 18/5,

which on the triangular lattice reads `P(D_n) = n^{-zeta+o(1)}` with
`zeta < 3/8`. Its §3.4 proposed to read off `zeta` from the CLE_6 event
"no loop meets both the negative real axis and the right half-plane".

**Setting (triangular site percolation, p = 1/2).** Let `B_n` be the
hexagon `{|j| <= n, |2i+j| <= 2n}` in axial coordinates, with boundary
sites black (wired). Let `I_n` be the black cluster of the boundary.
Let `S_n = {(i,0): -n < i <= 0}` and `X = {x > 0}`.

* *Circuit form* `D_n`: no white circuit in `B_n` surrounds a site of
  `S_n` and contains a site of `X`. This is the triangular analogue of
  the predecessor's box event.
* *Hull form* `H_n`: no component of `B_n \ I_n` (a hole of the wired
  cluster) contains both a site of `S_n` and a site of `X`. Hole
  boundaries are the interfaces that converge to CLE_6 loops, so `H_n` is
  the lattice form of the §3.4 event, with that event contained in it.

**Theorem 1.**
(a) `H_n ⊆ D_n`.
(b) `H_n` implies a black path in the closed upper half of `B_n`, from
    `{(0,0),(1,0)}` to a site at distance `>= n/2` from the origin. The
    same holds in the lower half. Hence
    `P(H_n) <= 2 pi^+(n/2) = n^{-1/3+o(1)}`, using the half-plane one-arm
    exponent `1/3`.
(c) `D_n` fails iff some white cluster `K` has an outermost white circuit
    (outer boundary of its filled set) that surrounds a site of `S_n` and
    meets `X`. A white circuit never passes through a *pinch*, which is a
    step whose two common neighbours both lie in `I_n` or outside the box,
    because it would then separate one of those `I_n` sites from `∂B_n`.
    So on `D_n \ H_n`, every hole joining `S_n` to `X` does so only
    through pinches.
    `tri_d.c` evaluates `D_n` through the proxy "no non-`I_n` path from
    `S_n` to `X` avoiding pinch steps". This is the predecessor's
    pinch-wall convention. The proxy implies `D_n` (proved), but the
    converse is not proved here.

**Numerics (`tri_d.c`, nested boxes).**
* Circuit-form proxy `D'_n` (pinch cuts on), 3000 samples at
  `n = 8..512`. The local slopes `-log2 P(D'_n | D'_{n/2})` lie in
  `0.267-0.306`; at `n = 512` the slope is `0.270(17)`, which excludes
  `3/8` by about 6 s.e. This is consistent with the Z^2 value `0.251(6)`
  of the predecessor (universality of `zeta`).
* Sanity check: `P(0 ∈ I_n)` has slopes `0.09-0.13`, matching the one-arm
  exponent `5/48 ≈ 0.104`.
* Hull form `H_n` (pinch cuts off), 3000 samples at `n = 8..256`.
  `P(H_n)` falls from `0.13` to `7e-4`, with local slopes `1.1-2`. The
  exponent is at least of order 1.

The table is in `results.txt`.

**Consequences.**
1. The §3.4 CLE_6 hull route cannot prove (H). Its event is a sub-event
   of `D_n` whose exponent is numerically `>= 1 > 3/8`. Rigorously, (b)
   only shows the exponent is `>= 1/3`, which does not by itself exclude
   the route. This obstruction is numerical, not a theorem.
2. The correct continuum object for `zeta` is (c): the event that no
   filled white cluster's outer boundary (an external perimeter,
   SLE_{8/3}-type, dimension 4/3) surrounds a point of the negative axis
   and enters the right half-plane. Pinch passages at four-arm points are
   exactly what separates it from the CLE_6 hull event.
3. A lower bound for `P(D_n)` built from a black crosscut next to the
   origin (as in (b)) costs at least the half-plane arm exponent `1/3`,
   which leaves a margin of only `1/24`. The full hull event, with
   crosscuts on both sides, is numerically far too rare. A proof of
   `zeta < 3/8` should therefore use configurations where holes do reach
   from `S_n` to `X`, but only through pinches.

**Next step.** Bound the exponent of the filled-cluster event (c) from
above by `3/8`. One candidate is an exploration along `S_n` that closes
fjords at pinch (four-arm) points. Another is the SLE_{8/3} / restriction
description of external perimeters, with a sub-event whose exponent is
computable, for example via the Beffara-type 3-arm/external-perimeter
calculus.
