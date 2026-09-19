---
rg: 2
id: excised-square-kills-cone-local-slit-pair-repair
kind: claim
title: A torus with one square excised into its own 1x1 torus has profile at most 2 and distance 1, yet every repair that touches only the cone component, including every chain of slit-pair swaps, costs at least n/4 - 1/2
distinct_from:
  two-torus-cross-slit-forces-sqrt-d-loss-in-thin-closing: that kills one-sided equivariant closing on the cross slit; here the two-sided slit-pair swap closes the cross slit at cost (1, 1), and the obstruction is to cone-local, excess-monotone surgery instead.
  centralizer-rounding-cannot-bound-rank-distance-by-profile: that is a one-sided centralizer bound; this bound holds for every commuting pair on the cone component, with both generators changed.
  slit-origami-z2-pair-has-rank-distance-half-l: that pair has large profile at its defect scale; here the profile is at most 2 and the whole pair is at distance 1.
  z2-bounded-rectangle-profile-forces-near-commuting: that is the open statement; this kills the slit-pair route to it (and padding-free rounding of permutation pairs) and leaves it open.
artifacts:
  - research/excised-square-kills-cone-local-slit-pair-repair-proof.md
  - experiments/slit-pair-swap-2026-09-17/swap.py
  - experiments/slit-pair-swap-2026-09-17/certify.py
  - experiments/slit-pair-swap-2026-09-17/summary.txt
---

**ESTABLISHED (unreviewed)** (`excised-square-kills-cone-local-slit-pair-repair-proof`). Elementary. An
obstruction to the slit-pair lemma proposed for `z2-bounded-rectangle-profile-forces-near-commuting`, and to any
repair of a permutation pair that works without padding.

**Slit-pair swaps.** Read a permutation pair `(b, c)` on `d` points as a square-tiled surface (`b` = right
neighbour, `c` = up neighbour). Take two grid-edge paths that follow the same word of moves (straight, left, right)
and use `2L` distinct edges. The *swap* exchanges the two gluings across each pair of corresponding edges. With `V`
vertical and `H` horizontal edges per path, it changes `b` by rank at most `V` and `c` by rank at most `H`.

**Calibration (cross slit).** On the coprime two-torus cross slit of
`two-torus-cross-slit-forces-sqrt-d-loss-in-thin-closing` (profile 2, distance 1), the shortest swap that lowers the
total cone excess has 2 edges (the two L-shaped slits), costs `(1, 1)` and gives a commuting pair. This holds for
every `p` from 3 to 7 (`certify.py`, part A). So two-sided swaps do close the family on which all one-sided routes
died.

**The family.** Fix `n >= 3`, let `(b0, c0)` be the unit translations of the torus `(Z/n)^2`, and let `x = (0,0)`.
Excise `x`: set `b(b0^-1 x) = b0 x`, `b(x) = x`, `c(c0^-1 x) = c0 x`, `c(x) = x`, and leave every other value as in
`b0, c0`.

**Theorem.** For every `n >= 3`:
1. `rank(b - b0) = rank(c - c0) = 1`, so `dist(b, c) <= 1` and `rho(b, c) <= 2`.
2. The surface is `S' ⊔ {x}`, where `{x}` is a flat `1 x 1` torus and `S'` (on `n^2 - 1` points) is connected, of
   genus 2, with a single cone point of angle `6 pi` (total excess 2).
3. Every commuting permutation pair `(b'', c'')` on the points of `S'` has
   `max(rank(b'' - b|S'), rank(c'' - c|S')) >= (n - 1 - n/p)/2 >= n/4 - 1/2`, where `p` is the least prime factor of
   `n`. For prime `n` the bound is `(n - 2)/2`.
4. Hence every slit-pair swap from the cone point that lowers the excess has at least `n/4 - 1/2` edges. Every chain
   of such swaps that ends at a commuting pair costs at least `n/4 - 1/2` in total. The same holds for every repair
   that changes only points of components containing a cone point.

**Computation** (`certify.py`, parts B and C).
- For `n` up to 40, the vertex structure in item 2 was checked directly.
- For `n <= 17`, the profile over `s, t <= 12` is at most 1.92.
- For `4 <= n <= 7`, every swap from the cone point with at most 10 edges was enumerated. The shortest lowering one
  has exactly `n - 1` edges and costs `(0, n - 1)`.

**What it kills.**
- *The slit-pair lemma as proposed.* At the cone point, every excess-lowering swap has length at least
  `n/4 - 1/2`, while `rho <= 2`. Iterating any cone-local, excess-lowering move cannot give `F(K)`.
- *Padding-free rounding of permutation pairs.* `S'` alone is a connected permutation pair with `rho(S') <= 2`. Its
  distance to commuting permutation pairs on the same points is at least `n/4 - 1/2`. With one padded point it is 1:
  put `x` back.
- *Excess as a monotone potential.* The optimal repair (put `x` back) is two unit swaps between `S'` and the flat
  donor `{x}`. The first one leaves the excess at 2 (`certify.py`, part B).

**Why it happens.** The obstruction is arithmetic, not geometric. The row and column cycles of length `n` that
survive a cheap repair force the big component to be a torus whose area divides `n^2`. The component has area
`n^2 - 1`, so the lost area has to come from outside it.

**Generic, not special.** Greedy iteration of the shortest lowering swap was run on 178 random clustered
perturbations of tori (part D). It got stuck (no lowering swap with at most 7 edges) in 13 cases. In 5 of them it had
stranded small flat tori of 1 or 2 squares beside an excess-2 component, the same mechanism.

**What it leaves.** A proof must include donor moves: excess-neutral swaps between a cone component and a flat torus
(an existing component, or a padded one, which the statement allows). The next target is the *donor slit-pair
lemma*. At a pair with profile `rho`, after padding by a flat torus of area `poly(rho)`, some chain of at most two
swaps with total length `poly(rho)` lowers the excess. By the Lipschitz bound
`rho(b', c') <= rho(b, c) + 2 max(rank(b' - b), rank(c' - c))` and `excess <= 2 rho`, this would prove the statement
for permutation pairs with an explicit (iterated) `F`.
