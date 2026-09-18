---
rg: 2
id: two-torus-cross-slit-forces-sqrt-d-loss-in-thin-closing
kind: claim
title: A two-torus cross-slit pair with profile 2, distance 1 and trivial period lattice covers only the one-square torus, where every rung closing costs at least 2p + 1 ~ sqrt(2d)
distinct_from:
  centralizer-rounding-cannot-bound-rank-distance-by-profile: that example ((Z/p)^2 x Z/2) covers the thick torus (Z/p)^2 with fibre of size 2, so Theorem B of the polynomial node already handles it; this example has period lattice Z^2, so the one-square torus is the only grid torus it covers, and Theorem B's thin construction is forced and costs ~sqrt(2d).
  regular-torus-covers-rank-distance-polynomial-in-profile: that proves dist <= 608 rho^4 (rho + |Y|); this shows that its thin construction (strip redirects plus rungs) loses at least sqrt(2d) on a family with rho <= 2 and dist = 1, and that neither proposed repair of the |Y| factor (support-weighted rungs, exact thick equivariant quotients) can work.
  nonabelian-band-rungs-absorb-ordered-charge-product: that proves the rung lemma; this shows that on the one-square torus the rung lemma is one-sided rounding, whose cost is not bounded by the profile when the period lattice is trivial.
  z2-bounded-rectangle-profile-forces-near-commuting: that is the open statement; this is an obstruction to two routes toward it and leaves it open.
artifacts:
  - research/two-torus-cross-slit-forces-sqrt-d-loss-in-thin-closing-proof.md
  - experiments/thin-period-obstruction-2026-09-17/twotorus.py
  - experiments/thin-period-obstruction-2026-09-17/twotorus-summary.txt
---

**ESTABLISHED (unreviewed)** (`two-torus-cross-slit-forces-sqrt-d-loss-in-thin-closing-proof`). Elementary. An
obstruction to the two routes proposed for removing the `|Y|` factor of Theorem B of
`regular-torus-covers-rank-distance-polynomial-in-profile`.

**The family.** Fix `p >= 2`. Let `T1 = (Z/p)^2` and `T2 = (Z/(p+1))^2`, and `Omega = T1 ⊔ T2`, so
`d = p^2 + (p+1)^2`. Let `b0, c0` be the unit translations on each torus, which commute. Take
`x1 = (0,0) in T1` and `x2 = (0,0) in T2`. Get `b` from `b0` by swapping the images of `x1` and `x2`, and `c` from
`c0` the same way. On the square-tiled surface, this glues the two tori along a unit cross slit at one vertex.

**Theorem.** For every `p >= 2`:
1. `dist(b, c) = 1` and `rho(b, c) <= 2`.
2. *(Trivial periods.)* Every map `pi : Omega -> Z^2/Lambda` with `pi b = pi + e1` and `pi c = pi + e2` has
   `Lambda = Z^2`. So the one-square torus is the only grid torus that `(b, c)` covers, with fibre `Y = Omega` and
   `|Y| = d`.
3. *(One-sided cost.)* Every `c'` that commutes with `b` has `rank(c' - c) >= 2p + 1`, and every `b'` that commutes
   with `c` has `rank(b' - b) >= 2p + 1`. Since `2p + 1 >= sqrt(2d) - 1`, the cost grows like `sqrt(2d)`.
4. *(The thin construction is one-sided here.)* On the one-square torus, the thin construction of Theorem B
   (Lemma 6 there) needs no push. Its only change is the rung of the single face, so its output keeps one
   generator. By (3), it costs at least `2p + 1`. Every closing that uses only rungs of the rung lemma is also
   one-sided, so it costs at least `2p + 1` too, however its values are chosen or weighted.

**What this kills.**
- *Route (i): weighting the redirects and rungs by holonomy support.* By (2), no strip cut exists: the base has one
  face. By (4), the rung is a one-sided rounding. So no weighting of the rung values can bring the cost below
  `2p + 1`, while `rho <= 2` and `dist = 1`. On pairs with trivial period lattice, the support-weighted thin
  closing is exactly the one-sided rounding that `centralizer-rounding-cannot-bound-rank-distance-by-profile` kills.
  The new point is that no choice of base torus avoids it.
- *Route (ii): an exact equivariant map onto a thick grid torus.* By (2), there is none, even though `rho <= 2` and
  both tori are thick (`lambda_1 = p` and `p + 1`). So a Rokhlin or tiling route must first do a surgery that is not
  equivariant. Here it is the cost-1 undo of the slit, and then each torus covers a thick torus.
- *Theorem B itself.* Its bound is `608 rho^4 (rho + d)`, and the thin construction it analyses provably costs at
  least `2p + 1 ~ sqrt(2d)` on this family. So the `|Y|` loss is real for that construction, not an artefact of the
  analysis. It is at least `sqrt(|Y|)`, and it is not bounded by any function of the profile.

**What it leaves.** Any proof of the forward statement for all permutation pairs has to leave the category of
covers of a fixed grid torus. It should work on the square-tiled surface directly and use two-sided surgery at the
cone points, with each generator changed only near the singular set:
- here the surface has genus 2 and two cone points of angle `4 pi`, and the undo of the slit changes one site of `b`
  and one site of `c`;
- in general, `rank([b,c] - I) <= 2 rho` bounds the total cone excess, so the genus is at most `rho + 1`.

The natural next target is then a *slit-pair lemma*. If a cone point `q` has cone angle excess, is there a pair of
parallel saddle connections (or unit slits) of `l^1` length `poly(rho)` near `q` whose swap lowers the total
excess? Such a lemma, iterated at most `2 rho` times, would give `F = poly(K)` for all permutation pairs.

**Computation** (`twotorus.py`, `twotorus-summary.txt`). For `2 <= p <= 15`:
- `rank(b - b0) = rank(c - c0) = 1`;
- the gcd of the cycle lengths of `b` and of `c` is 1;
- the exact least number of disagreements of one-sided roundings, by assignment over cycles of equal length with all
  rotations, is `4p + 2` in both directions. The proof gives exactly this bound, so the rank is at least `2p + 1`.
- the profile, scanned over `s, t <= 12` for `p <= 9`, stays below 2 in every case (its largest value is 1.9, at `p = 9`).

All assertions pass.
