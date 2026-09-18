---
rg: 2
id: centralizer-rounding-cannot-bound-rank-distance-by-profile
kind: claim
title: Keeping one word b^v1 c^v2 fixed and rounding the other generator in its centralizer cannot bound the rank distance by the rectangle profile, since a cross-slit pair with profile 2 and distance 1 forces cost 2p in every frame of norm below p
distinct_from:
  z2-bounded-rectangle-profile-forces-near-commuting: that is the open forward statement; this kills one proof strategy for it (one-sided centralizer or conjugator rounding in a GL2(Z) frame, including band surgery with conjugating fibre bijections) and leaves the statement open.
  torus-abelian-covers-rectangle-profile-near-commute: that proves the statement for abelian torus covers, using band surgery only in its thin case, where lambda_1 is bounded by the profile; this shows that the thin-case surgery does not transplant to non-abelian fibres, because over the one-square torus every permutation pair is thin and the conjugator cost is at least 2p while the profile is 2.
  z2-commuting-pairs-are-not-bounded-rank-stable: that shows a bounded commutator rank does not force near-commuting; here the pair is already at distance 1 and the lower bound is for a restricted class of roundings, not for the distance.
  near-exact-tuples-saturate-linear-conversion-defect: that proves the converse (distance delta gives profile at most 2 delta), which is used here to bound the profile of the example by 2.
artifacts:
  - research/centralizer-rounding-cannot-bound-rank-distance-by-profile-proof.md
  - experiments/nonabelian-rectangle-profile-2026-09-17/perm.py
  - experiments/nonabelian-rectangle-profile-2026-09-17/crossframes.py
  - experiments/nonabelian-rectangle-profile-2026-09-17/crossslit.py
  - experiments/nonabelian-rectangle-profile-2026-09-17/sweep1.py
  - experiments/nonabelian-rectangle-profile-2026-09-17/thin1.py
  - experiments/nonabelian-rectangle-profile-2026-09-17/t0.py
  - experiments/nonabelian-rectangle-profile-2026-09-17/summary.txt
---

**ESTABLISHED (unreviewed)** (`centralizer-rounding-cannot-bound-rank-distance-by-profile-proof`).
Elementary. An obstruction: it kills a class of approaches to
`z2-bounded-rectangle-profile-forces-near-commuting`.

**The strategy it kills.** The thin case of `torus-abelian-covers-rectangle-profile-near-commute` works as
follows. Change generators to `B = b^v1 c^v2`, `C = b^u1 c^u2` with `det(v,u) = 1`. Keep `B` exactly,
replace `C` by some `C'' in C(B)` (band surgery), and back-substitute `b'' = B^u2 C''^-v2`,
`c'' = B^-u1 C''^v1`. The planned extension to non-abelian fibres does the same, regluing each band by
a fibre bijection that conjugates one row monodromy of `B^k` into the other. Every such rounding
produces a commuting pair `(b'', c'')` with `b''^v1 c''^v2 = b^v1 c^v2`. The hope was a cost bounded
by a function of the rectangle profile `rho`.

**Theorem.** Let `p >= 5` be prime and `h = (p-1)/2`. On `Omega = (Z/p)^2 x Z/2` (`2p^2` points),
put `P = (0,0)`, `Q = (0,h)`, and
`b(x,e) = (x + e1, e + [x = P])`, `c(x,e) = (x + e2, e + [x = Q])`.
(Here `b^v1 c^v2` means: apply `c^v2` first.) Then:
1. `dist(b,c) <= 1` and `rho(b,c) <= 2`, where equality holds for `p = 11, 13, 17` (exact computation).
2. Let `v` be primitive with `|v1| + |v2| <= p-1`. Let `(b'', c'')` be any commuting pair of
   permutations of `Omega` with `b''^v1 c''^v2 = b^v1 c^v2`. If `v1 != 0` then `rank(c'' - c) >= 2p`.
   If `v1 = 0` then `rank(b'' - b) >= 2p`.
3. The same holds with the roles of `v` and `u` swapped, i.e. when `C = b^u1 c^u2` is the word kept.

So one-sided rounding in any frame whose kept vector has `l^1` norm below `p` costs at least
`2p = sqrt(2n)`, while `rho <= 2`. This includes `v = e1` (keep `b`, round `c` in `C(b)`).
No function of `rho` bounds this cost.

**Why this kills the non-abelian thin step.** Every permutation pair is a cover of the one-square
torus, with fibre `Omega`. For that base `lambda_1 = 1`, the thin frame is `v = e1`, and band
surgery is exactly "keep `b`, round `c` in `C(b)`, i.e. conjugate the row monodromy". Part 2 with `v = e1`
shows the conjugating fibre bijection costs at least `2p` although `rho <= 2`. The same pair, read as a
`Z/2`-cover of the `p x p` torus, has `lambda_1 = p` and four clustered charges. There,
`torus-abelian-covers-rectangle-profile-near-commute` rounds it by a two-sided local path cut, which
is consistent with dist = 1.

**Where it fails, exactly.** The kept word `B` has 2p-cycles on the fibres over a nonempty proper
set `J` of its base orbits. The generator to be rounded moves that set to `J + v1` (or `J - v2`), a
different set. Any `c''` commuting with `B` makes `theta = c c''^-1` a conjugator from `B` to `c B c^-1`,
so `theta` must move all `4p` or more points in the symmetric difference.

**What it leaves.** Any proof of the forward statement has to be two-sided and local near the defect:
it must change both generators (as the path cuts of the abelian proof do), or keep a word of norm at
least of the order of the defect scale. For abelian dipoles, direct two-sided strip cuts along digital
lines are the natural route to an `O(rho)` bound.

**Computation** (`experiments/nonabelian-rectangle-profile-2026-09-17/summary.txt`):
- `crossframes.py p` checks parts 1 and 2 for every primitive frame vector with `|v|_1 <= p-1`:
  128, 184 and 320 frames for `p = 11, 13, 17`, with no failure and exact profile 2.
- `crossslit.py` gives a cylinder variant on `2lL` points, with `dist <= 1` and `rho = 2`. There the
  best exact one-sided rounding over all frames with entries at most 1 costs `2 min(l,L) + 1`.
- `sweep1.py` and `thin1.py` compare the exact profile with the best one-sided frame rounding on
  random `S_3`, `Q_8` and `A_4` slit covers.

## Attempts
