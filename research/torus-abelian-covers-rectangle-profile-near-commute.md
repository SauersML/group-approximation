---
rg: 2
id: torus-abelian-covers-rectangle-profile-near-commute
kind: claim
title: Permutation pairs that are abelian covers of a square-tiled torus and have rectangle profile at most K lie within rank exp(O(K log K)) of a commuting pair, and within 3072 K^4 for dipole covers
distinct_from:
  z2-bounded-rectangle-profile-forces-near-commuting: that is the open statement for all unitary pairs (and all permutation pairs); this proves it for the class of abelian torus covers, with a GL2(Z) basis change that closes the "all short saddle connections diagonal" gap recorded in its Attempts.
  slit-origami-z2-pair-has-rank-distance-half-l: that computes the distance of one Z/2 dipole cover with a horizontal slit; this bounds the distance of every abelian torus cover by its rectangle profile, and the slit origami is the calibration case of Theorem A.
  z2-commuting-pairs-are-not-bounded-rank-stable: that shows a bounded commutator rank does not force near-commuting; here the hypothesis is the whole rectangle profile, and the far-from-commuting examples there have profile growing with their defect scale, consistent with this theorem.
  near-exact-tuples-saturate-linear-conversion-defect: that proves the converse (distance delta gives profile at most 2 delta); this is a forward direction on one class.
artifacts:
  - research/torus-abelian-covers-rectangle-profile-near-commute-proof.md
  - experiments/rectangle-profile-dipoles-2026-09-17/dc.c
  - experiments/rectangle-profile-dipoles-2026-09-17/anneal.c
  - experiments/rectangle-profile-dipoles-2026-09-17/sweep.sh
  - experiments/rectangle-profile-dipoles-2026-09-17/lam.py
  - experiments/rectangle-profile-dipoles-2026-09-17/surgery.py
  - experiments/rectangle-profile-dipoles-2026-09-17/summary.txt
---

**ESTABLISHED (unreviewed)** (`torus-abelian-covers-rectangle-profile-near-commute-proof`). Elementary.
This is the forward direction of `z2-bounded-rectangle-profile-forces-near-commuting` on a class of
permutation pairs with an unbounded number of squares. The bound is not the `O(K^2)` asked for,
but it does not depend on the number of squares.

**Class.** Let `Lambda <= Z^2` have finite index `N`, `G = Z^2/Lambda`, and let `A` be a finite
abelian group. For any functions `beta, gamma : G -> A` put, on `Omega = G x A`,
`b(x,a) = (x + e1, a + beta(x))` and `c(x,a) = (x + e2, a + gamma(x))`. These are the square-tiled
surfaces that are regular `A`-covers of an `N`-square torus, branched at vertices. The **charge**
`kappa(x) = beta(x) + gamma(x+e1) - gamma(x) - beta(x+e2)` is the monodromy around the vertex at `x`.
The pair commutes iff `kappa = 0`. Let `n = |supp kappa|` and let `lambda_1` be the least `l^1` norm of
a nonzero vector of `Lambda`.

**Profile and distance.** `rho = sup_(s,t >= 1) rank([b^s,c^t] - I)/(s+t)`, and
`dist = min max(rank(b'-b), rank(c'-c))` over commuting permutation pairs `(b',c')` on `Omega`.
No padding is needed.

**Theorem B (all abelian torus covers).** `dist <= exp(O(rho log rho))`. Explicitly, with `K = rho`,
`r_0 = floor(8K) + 1` and `Lambda_0 = 16 K r_0 (8K + 2)^(4K)`,
`dist <= max(24 K Lambda_0^4, 8 K r_0 (8K+2)^(4K))`.

**Theorem A (dipole covers).** Suppose `kappa = a delta_(x_0) - a delta_(x_0 + g)`. Let
`m_0 = min(|g|_1, lambda_1)`, with `|g|_1` the least `l^1` norm of a lift of `g`. Then:
- `rho >= |A| ceil(m_0/2) / 2`;
- if `|g|_1 <= lambda_1`, then `dist <= |A| |g|_1 <= 4 rho`;
- otherwise `dist <= 12 |A| lambda_1^4 <= 3072 rho^4`.

So `F(K) <= 3072 K^4` on dipole covers.

**The step that closes the diagonal gap.** Take the shortest vector `w = k v` of `Lambda`, with `v`
primitive. Complete `v` to a basis `(v, u)` of `Z^2` with `|u|_inf <= |v|_inf`. Then pass to
`B = b^(v1) c^(v2)` and `C = b^(u1) c^(u2)`.
- `B` translates along the short closed direction, so the base splits into `N/k` rows (`B`-orbits)
  of length `k <= lambda_1`.
- The `B`-monodromy `eps_j` of row `j` jumps only across rows that carry charge.
- Cut `C` at the last row of each maximal band of constant `eps` and reglue that row to the band's
  first row. Each band becomes a torus on which every row has total charge 0.
- Cancel the charges inside each row by changing fibre values of `C`. The result `C''` commutes with `B`.
- Back-substitute `b'' = B^(u2) C''^(-v2)` and `c'' = B^(-u1) C''^(v1)`. These commute.
  The cost is `rank <= 6 |A| n lambda_1^4`.

This handles cone points whose short saddle connections are all diagonal: the short direction
becomes a generator, and the diagonal length only enters through `|v|_inf <= lambda_1`.

When `lambda_1` is large (the fat case), a hierarchical clustering of the charges works. Take levels
`r_j = r_0 (2n+2)^j`.
- Some consecutive pair of levels gives the same clusters.
- A cluster with nonzero total charge is then isolated inside a `2n r_j` square, and that square has
  rectangle rank at least `|A|(n+1)^2 r_j^2/2 > 2 (2n r_j) rho`. So no such cluster exists.
- Neutral clusters are cancelled along spanning trees at cost `<= 2|A| n r_(n-1)`.

**Computation** (`experiments/rectangle-profile-dipoles-2026-09-17/`, `summary.txt`).
- **Scope.** Z/2 dipole covers on every Hermite-normal-form lattice with `N <= 40` (35205 cases, exact
  `rho` by `dc.c`).
- **Profile.** `min(|g|_1, lambda_1)/rho` lies in `[0.525, 1.714]`, as Theorem A predicts.
- **General loops.** For `N <= 26` (9440 cases), annealing over all region-boundary loops (`anneal.c`)
  never beats the rectangle profile by more than a factor of `1.25`. So general words add at most
  that factor over rectangles.
- **Explicit constructions.** For `N <= 22` (5749 cases), `surgery.py` builds both commuting pairs
  explicitly and checks commutation. The cheaper one has `rank(b''-b) + rank(c''-c) <= 2.5 rho` in
  every case.
- **What this rules out.** No Z/2 dipole cover with `N <= 22` has distance above `2.5 rho`. So
  in this range the distance is linear in `rho`, and the `K^4` looks like an artefact of the thin-case
  bookkeeping.

**What is left for the permutation case of the target.**
- Every permutation pair is a (non-abelian) cover of the one-square torus, so the class above is the
  abelian part of the problem.
- The clustering and tree cancellation should extend to non-abelian fibres, with costs counted on
  supports. This has not been checked in detail.
- The thin surgery does not extend. The `eps_j` become permutations of an unbounded fibre, and bands
  of conjugate rather than equal monodromy need a fibre isomorphism before regluing. That
  isomorphism's rank cost is the open quantity.
