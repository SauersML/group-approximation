---
rg: 2
id: regular-torus-covers-rank-distance-polynomial-in-profile
kind: claim
title: Every regular F-cover of a square-tiled torus lies within rank 10^4 rho^4/|F|^3 of a commuting pair, and every cover with fibre Y within 608 rho^4 (rho + |Y|)
distinct_from:
  nonabelian-two-charge-torus-covers-rank-distance-linear: that needs at most two charged faces; this allows any number of charges, with the missing multi-charge lower bound supplied by threshold box clusters.
  torus-abelian-covers-rectangle-profile-near-commute: that is abelian, with the bound exp(O(K log K)); this allows any finite fibre group and gives O(K^4), with K = rho/|F|.
  torus-dipole-covers-rank-distance-linear-in-profile: that is one abelian dipole; this is the general charge configuration.
  nonabelian-band-rungs-absorb-ordered-charge-product: that is the band-closing tool used here; this adds the lower bound and the cluster surgery.
  z2-bounded-rectangle-profile-forces-near-commuting: that is the open statement for all pairs; this proves a polynomial F(K) for all regular torus covers, and for all covers with fibre Y at the cost of a |Y| factor on thin tori.
artifacts:
  - research/regular-torus-covers-rank-distance-polynomial-in-profile-proof.md
  - experiments/nonabelian-rectangle-profile-2026-09-17/multicharge.py
  - experiments/nonabelian-rectangle-profile-2026-09-17/multicharge-summary.txt
---

**ESTABLISHED (unreviewed)** (`regular-torus-covers-rank-distance-polynomial-in-profile-proof`). Elementary.

**Class.** `Lambda <= Z^2` has index `N`, and `G = Z^2/Lambda`. A *cover of `G` with fibre `Y`* is a permutation pair
`(b, c)` of a finite set `Omega` with a map `pi : Omega -> G` such that `pi b = pi + e1` and `pi c = pi + e2`. All
fibres then have the same size `m = |Y|`, and after identifying each fibre with `Y`:
- `b(x,y) = (x+e1, beta(x) y)` and `c(x,y) = (x+e2, gamma(x) y)`, with `beta, gamma : G -> Sym(Y)`;
- the face holonomy is `hol(x) = gamma(x)^-1 beta(x+e2)^-1 gamma(x+e1) beta(x)`, and the pair commutes iff every face
  is flat;
- the cover is *regular* when `Y = F` is a finite group acting on itself by left multiplication, so that
  `beta, gamma` take values in `F`.

Also:
- `rho = sup_(s,t>=1) rank([b^s,c^t]-I)/(s+t)`;
- `lambda_1` is the least `l^1` norm of a nonzero vector of `Lambda`;
- `dist` is the least `max(rank(b'-b), rank(c'-c))` over commuting pairs `(b', c')` of `Omega`.

**Theorem A (regular covers).** For every finite group `F` and every regular `F`-cover of a grid torus, with any
number of charged faces, `dist <= 10^4 rho^4/|F|^3`. With `K = rho/|F|`, this is `dist <= 10^4 K^4 |F|`, and
since `|F| >= 2` whenever some face is charged, `dist <= 1250 rho^4`.

**Theorem B (any fibre).** For every cover of a grid torus with fibre `Y`, `dist <= 608 rho^4 (rho + |Y|)`. On thick
tori, `lambda_1 >= 96 rho^3`, the bound is `dist <= 384 rho^5`, independent of `|Y|` and of `N`.

**The multi-charge lower bound.** This is the step the two-charge node lacked.
- Cluster the lifted charges in the plane at a threshold `theta`: merge two clusters when translates of their
  bounding boxes come within `l^inf` distance `theta`. A cluster of `k` charges has a bounding box of side at most
  `(k-1) theta + 1`.
- A cluster is *neutral* when the boundary of its bounding box has trivial holonomy.
- If a cluster is not neutral and `lambda_1 >= 2(n+1) theta`, there are `(theta+1)^2` boxes whose only charges are
  that cluster. Each has boundary holonomy conjugate to the cluster's, and they have distinct corners. So
  `rho > theta sigma / (4(n+1))`, where `sigma` is the support size of the cluster holonomy on `Y`.
- **The replacement for `|F|/2`.** A permutation `W` of `Y` has `rank(W - I) >= |supp W|/2`, so the right weight
  of a charge is the support size of its holonomy.
  - On regular fibres, `sigma = |F|`.
  - In general, `sigma >= 2`, and the charged faces satisfy `sum supp hol(q) <= 4 rho`, so `n <= 2 rho`.
  - The support weights also bound the cost of the surgery: a push changes an edge by a conjugate of the current
    face holonomy, and supports are subadditive.

So `theta ~ 4 (n+1) rho/|F|` (regular) or `theta ~ 2 (n+1) rho` (general) forces every cluster to be neutral.

**Constructions.**
- *Thick* (`lambda_1 >= 2(n+1) theta`): push every charge of each neutral cluster to a corner of its box. At most
  `2 n^2 theta` sites change, and each costs at most the total support of its cluster.
- *Thin*: cut the torus into row strips at every gap of more than `2l` rows between charged rows (at most `n`
  pieces). Walk each charge at most `2n` steps into a digital band of its piece, and close each band with the rung
  lemma. At most `3 n lambda_1 + 2 n^2` sites change.

**What is new.** The two-charge node needed its lower bound case by case. Threshold clustering makes the lower bound
uniform in the number of charges, and so the strip cut at every charged-row gap works in general. The polynomial
`O(K^4)` improves the abelian `exp(O(K log K))` of `torus-abelian-covers-rectangle-profile-near-commute`, in a more
general class.

**Limits.**
- *The fibre factor.* In the thin case, each strip redirect and each rung changes one whole fibre, at cost `|Y|`.
  Every permutation pair on `d` points is a cover of the one-square torus with `|Y| = d`, so Theorem B says nothing
  unless `|Y|` is small compared with `d`. Removing the `|Y|` factor on thin tori would prove the target for all
  permutation pairs.
- *Linear.* Single-scale box counting does not seem to give `dist = O(rho)`. A heuristic multi-scale `Z/2` example
  (dense small dipoles hiding larger ones) suggests that the ratio `dist/rho` of these constructions can grow like
  `log N / log log N`. This is not proved, and it is recorded as open.

**Computation** (`multicharge.py`, `multicharge-summary.txt`). Both constructions ran on 600 covers:
- fibres `S_3`, `Q_8` and `A_4` (regular), and `S_3` on 3 points and `S_4` on 4 points (not free);
- thin, random and thick tori with `N <= 484`, and up to 13 charges.

All assertions pass: the box-count lemma on every non-neutral cluster, flatness, the site bounds, and the bounds of
Theorems A and B with `rho` replaced by `rho_lower <= rho`. The worst `dist/rho_lower` was `1.56` for the cluster
construction and `52` for the strip construction.
