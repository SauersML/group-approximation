---
rg: 2
id: torus-dipole-covers-rank-distance-linear-in-profile
kind: claim
title: Abelian dipole covers of a square-tiled torus lie within rank 24 rho of a commuting pair, by a two-sided strip cut along the shortest lattice direction
distinct_from:
  torus-abelian-covers-rectangle-profile-near-commute: that proves dist <= 3072 rho^4 for dipole covers, using one-sided band surgery (keep B = b^v1 c^v2, round C in its centralizer, back-substitute), whose cost carries lambda_1^4 from long staircase words; this proves dist <= 24 rho for the same class, with a different surgery that changes b and c directly near two cut lines and never passes to the words B, C. It uses only the lower bound of that note.
  z2-bounded-rectangle-profile-forces-near-commuting: that is the open statement for all unitary (and all permutation) pairs, with F(K) = O(K^2) asked for; this gives F(K) <= 24 K on the class of abelian dipole torus covers, which is linear and does not depend on the number of squares.
  centralizer-rounding-cannot-bound-rank-distance-by-profile: that shows one-sided rounding with a kept word cannot work in general; this is the two-sided local surgery that obstruction points to, carried out for abelian dipoles.
  slit-origami-z2-pair-has-rank-distance-half-l: that computes the distance of one dipole cover exactly; this bounds all of them linearly in the profile.
artifacts:
  - research/torus-dipole-covers-rank-distance-linear-in-profile-proof.md
  - experiments/nonabelian-rectangle-profile-2026-09-17/strips.py
  - experiments/nonabelian-rectangle-profile-2026-09-17/strips_band.py
  - experiments/nonabelian-rectangle-profile-2026-09-17/strips_thin.py
  - experiments/nonabelian-rectangle-profile-2026-09-17/perm.py
  - experiments/nonabelian-rectangle-profile-2026-09-17/strips-summary.txt
---

**ESTABLISHED (unreviewed)** (`torus-dipole-covers-rank-distance-linear-in-profile-proof`). Elementary.
It sharpens Theorem A of `torus-abelian-covers-rectangle-profile-near-commute` from `3072 rho^4` to
`24 rho`.

**Class.** Notation of `torus-abelian-covers-rectangle-profile-near-commute`: `Lambda <= Z^2` of index
`N`, `G = Z^2/Lambda`, `A` a finite abelian group, `Omega = G x A`,
`b(x,a) = (x+e1, a+beta(x))`, `c(x,a) = (x+e2, a+gamma(x))`, and charge
`kappa(x) = beta(x) + gamma(x+e1) - gamma(x) - beta(x+e2)`. The pair is a **dipole cover** if
`kappa = a delta_(x_0) - a delta_(x_0+g)` with `a != 0`. `lambda_1` is the least `l^1` norm of a nonzero
vector of `Lambda`, and `|g|_1` the least `l^1` norm of a lift of `g`.
`rho = sup_(s,t>=1) rank([b^s,c^t]-I)/(s+t)`, and `dist` is the least `max(rank(b'-b), rank(c'-c))`
over commuting permutation pairs `(b',c')` of `Omega`.

**Theorem.** For every dipole cover, `dist <= 24 rho`. More precisely:
- if `|g|_1 <= lambda_1`, then `dist <= |A| |g|_1 <= 4 rho` (Theorem A of the torus note);
- otherwise `dist <= 6 |A| lambda_1 <= 24 rho`.

Together with the converse `rho <= 2 dist` (`near-exact-tuples-saturate-linear-conversion-defect`),
`rho` and `dist` agree up to the factor 24 on this class. The class has unbounded `N`,
unbounded `|g|_1 / lambda_1`, and arbitrary finite abelian fibre.

**The surgery.**
1. Take a shortest `w = k v` in `Lambda`, `v` primitive, `l = |v|_inf`, and `det(v,u) = 1`.
   The row index `r(x) = det(v, x) mod L` with `L = N/k` is well defined on `G`. Its fibres are the `k`-point orbits of
   the translation by `v`.
2. Let `D` be the cyclic row distance between the two charges.
   - If `D <= 2l`, the dipole is short: `|g|_1 < 3.54 lambda_1`, and the path cut costs `|A| |g|_1`.
   - Otherwise cut the row circle at the two charges. Piece `I_1` is the shorter arc from one charge to the
     other, and `I_2` is the rest; both have height `>= 2l`.
3. Reglue each piece into its own torus `Z^2/<w, H u>`. The b- and c-moves that cross a cut line are
   redirected by `-+H u`. There are `2 lambda_1` such moves, since each cut line is crossed by
   `k|v2|` b-moves and `k|v1|` c-moves.
4. Keep all fibre values. The new charges lie in the seam zone of width `2l`. They sum to 0 on each piece torus.
   Each is at most one grid step from the **band** `{sigma <= det(v,.) < sigma + |v|_1}`. This band
   is a closed grid cycle of exactly `lambda_1` vertices.
5. Cancel along the band. This costs at most `4 lambda_1` fibre changes in total, plus the `2 lambda_1` redirects.

The lower bound `rho >= |A| ceil(lambda_1/2)/2` of the torus note then turns `6|A| lambda_1` into `24 rho`.

**Computation** (`experiments/nonabelian-rectangle-profile-2026-09-17/strips-summary.txt`):
- `strips_band.py` carries out exactly the construction of the proof for `Z/2` dipoles. On every strip case it
  asserts the redirect count, the charge support, the seam zone, the band size and connectivity, the one-step
  adjacency and the `6 lambda_1` count. It also checks commutation and exact ranks against the exact profile.
  - Exhaustively over all HNF tori with `N <= 20` and all `g`: 4342 cases, 1242 strip cases, all assertions pass.
  - On long thin tori (`N1 <= 4`, `N2 <= 48`, two seeds): 540 cases.
  - The construction's `dist/rho` is at most `4.5`, and changed sites are at most `3.34 lambda_1`.
- `strips.py` (exhaustive, `N <= 16`, 2233 cases) takes the best of the path cut and all two-cut strip surgeries.
  Its worst `dist/rho` is `1.667`, so the constant 24 is far from sharp.
- On thin tori, the path-cut cost `|g|_1/rho` reaches `9.5`, so the strip cut is needed.

**What it leaves.**
- *Several charges.* Cutting at every charged row should give `O(|A|(n lambda_1 + n^2))` for the thin case of
  Theorem B. This is not proved, because the merged clusters need not be neutral.
- *Theorem B.* Its exponential comes from the fat-case clustering, not from the thin case.
- *Non-abelian fibres.* Cancellation inside a piece needs the ordered product of the charges around the band
  to be trivial, not just their sum. That is the next step.

## Attempts
