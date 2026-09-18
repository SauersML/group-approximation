---
rg: 2
id: regular-torus-covers-rank-distance-polynomial-in-profile-proof
kind: route
target: regular-torus-covers-rank-distance-polynomial-in-profile
requires:
  - nonabelian-band-rungs-absorb-ordered-charge-product
  - nonabelian-two-charge-torus-covers-rank-distance-linear
  - torus-dipole-covers-rank-distance-linear-in-profile
title: Threshold box clusters give a multi-charge lower bound; corner pushes on thick tori and a strip cut at every charged-row gap on thin tori give dist <= 10^4 rho^4/|F|^3
---

Notation as in the claim. We cite three nodes:
- *[R]* is `nonabelian-band-rungs-absorb-ordered-charge-product`: Theorem 1 (rung lemma), its Corollary, and the van
  Kampen fact that the boundary holonomy of a disk of faces is a product of conjugates of its face holonomies. [R] is
  stated for any group, so it applies to `Sym(Y)`.
- *[T]* is `nonabelian-two-charge-torus-covers-rank-distance-linear-proof`: Lemma 3 (push) and the paragraph
  "single charge on `G`", which shows that for every `sigma` the window `{sigma <= det(v,.) < sigma + |v|_1}`
  projects to a band of `lambda_1` faces of `G` in the sense of [R].
- *[D]* is `torus-dipole-covers-rank-distance-linear-in-profile-proof`: Section 2 (`w = k v`, `l = |v|_inf`,
  `u`, the row index `r`, `L = N/k`, the pieces `I`, the tori `T_I`, and Lemma 2) and Lemmas 3 and 4. These are
  statements about the lattice only.

Let `Q` be the set of charged faces, `n = |Q|`, and, for a permutation `W` of `Y`, let `sigma(W) = |supp W|`.
Put `S = sum_(q in Q) sigma(hol q)`. Note `sigma(W) = sigma(W^-1) = sigma(A W A^-1)`, and
`sigma(W W') <= sigma(W) + sigma(W')`. On a regular fibre, `sigma(W) = |F|` for every `W != 1`.

A *site* is `(x, b)` or `(x, c)`. Changing `beta(x)`, changing `gamma(x)`, or redirecting the base move at `x`
changes one permutation on one fibre, so it costs rank at most `m = |Y|`. Changing `beta(x)` to `beta(x) D`, or
to `D beta(x)`, costs rank at most `sigma(D)`, because the two permutation matrices differ by a factor
`P_D - I` of rank at most `sigma(D)`.

We assume `lambda_1 >= 2` and `n >= 1`. If `n = 0`, then `dist = 0`. If `lambda_1 = 1`, the base is a cycle, and the
proof of the thin case below applies with the band of one face bordering itself, as in [T].

## 1. Lower bounds

**Lemma 1.** Fix `s, t >= 1`. On the fibre over `x`, `[b^s, c^t]` acts by a permutation `W_x` of `Y`, which is the
holonomy of the boundary of an `s x t` box `R_x` of faces with a corner at a lift of `x`. So
`rank([b^s,c^t] - I) >= (1/2) sum_(x in G) sigma(W_x)`. In particular (`s = t = 1`) `rho >= S/4`, so:
- `n <= 2 rho`, and `S <= 4 rho`, in general;
- `n <= 4 K` with `K = rho/|F|`, on regular fibres.

*Proof.* The base maps are the commuting translations, so the commutator preserves each fibre, and its value there
is the product of the edge values along the boundary of `R_x`. A permutation `W` has
`rank(P_W - I) = sigma(W) - (number of cycles of W on supp W) >= sigma(W)/2`, and the fibres are disjoint.
For `s = t = 1`, `W_x` is conjugate to `hol(x)^(±1)`. Finally, `sigma(W) >= 2` for `W != 1`. QED.

**Clusters.** Work in the plane with the lifted charged set `Q~ = pi^-1(Q) ⊂ Z^2`. Faces are unit cells, and for
finite sets `A, B` of cells, `d(A, B)` is the least `l^inf` distance between their cells: adjacent cells have
distance 1. For a finite set `P` of cells, `bb(P)` is its bounding box, and `w(P)`, `h(P)` are its width and
height.

Fix `theta >= 1`. Start with one singleton `{q~}` for a chosen lift of each `q in Q`. While two clusters `P != P'`
and some `lambda in Lambda` satisfy `d(bb P, bb P' + lambda) <= theta`, replace them by `P ∪ (P' + lambda)`.

**Lemma 2.** Suppose `lambda_1 >= 2(n+1) theta`. The procedure stops, and the final clusters `P` satisfy:
- (a) `P` projects injectively into `Q`, the projections of the clusters partition `Q`, and
  `w(P), h(P) <= (|P| - 1) theta + 1 <= n theta`;
- (b) the projection of `bb P` to `G` is injective;
- (c) for `lambda != 0`, `d(bb P, bb P + lambda) > theta`, and for final clusters `P != P'` and every `lambda`,
  `d(bb P, bb P' + lambda) > theta`;
- (d) the cells of `Q~` at distance at most `theta` from `bb P` are exactly the cells of `P`.

*Proof.* Each merge lowers the number of clusters, so the procedure stops. The projections partition `Q` at the start,
and a merge joins two clusters with disjoint projections, so the first part of (a) holds throughout.

The width bound in (a) is by induction. A singleton has width 1. If `d(bb P, bb P'') <= theta`, the x-extents of the
two boxes overlap or leave a gap of at most `theta - 1` columns. So
`w(P ∪ P'') <= w(P) + w(P'') + theta - 1 <= (|P| + |P''| - 1) theta + 1`. The height is the same.

(b) Two cells of `bb P` differ by a vector of `l^1` norm at most `2 n theta - 2 < lambda_1`.

(c) The second part is the stopping rule. For the first, let `lambda != 0`. Then
`|lambda|_inf >= lambda_1/2 >= (n+1) theta`, and the gap between `bb P` and `bb P + lambda` in the coordinate
where `|lambda|` is largest is `|lambda|_inf - (side) + 1 >= (n+1) theta - n theta + 1 > theta`.

(d) Every cell of `Q~` lies in `P' + lambda` for a unique final cluster `P'` and a unique `lambda`, by (a). If
`(P', lambda) != (P, 0)`, then (c) puts it at distance more than `theta` from `bb P`. QED.

Call a final cluster *neutral* if the boundary of `bb P` has trivial holonomy, and write `hol(∂P)` for that
holonomy (based at the lower-left corner). Its support size `sigma(hol ∂P)` does not depend on the base point.

**Lemma 3 (box count).** Suppose `lambda_1 >= 2(n+1) theta`, and let `P` be a final cluster that is not neutral,
with `sigma_P = sigma(hol ∂P)`. Then `rho > theta sigma_P / (4(n+1))`.

*Proof.* Let `bb P` have lower-left cell `(x_0, y_0)` and size `w x h`. For `0 <= i, j <= theta`, let `R_(ij)` be the
box with lower-left cell `(x_0 - i, y_0 - j)` and size `s x t`, where `s = w + theta` and `t = h + theta`.
- `R_(ij)` contains `bb P`, and every cell of `R_(ij)` is at distance at most `theta` from `bb P`. By Lemma 2(d), the
  charged cells of `R_(ij)` are exactly those of `P`.
- The faces of `R_(ij) \ bb P` are flat. That region is an annulus of flat faces, so by the van Kampen fact of [R]
  the boundary holonomies of `R_(ij)` and `bb P` are conjugate: `W` for the corner of `R_(ij)` is conjugate to
  `hol(∂P)^(±1)`, and `sigma(W) = sigma_P`.
- The corners differ by vectors of `l^1` norm at most `2 theta < lambda_1`, so they are `(theta+1)^2` distinct points
  of `G`.

By Lemma 1, `rank([b^s, c^t] - I) >= (theta+1)^2 sigma_P / 2`. Also `s + t <= 2 n theta + 2 <= 2(n+1) theta`,
by Lemma 2(a). So `rho >= (theta+1)^2 sigma_P / (4(n+1) theta) > theta sigma_P / (4(n+1))`. QED.

**Corollary 4 (all clusters are neutral).** Suppose `lambda_1 >= 2(n+1) theta`.
- Regular fibres: if `theta >= 4(n+1) K`, every final cluster is neutral.
- Any fibre: if `theta >= 2(n+1) rho`, every final cluster is neutral.

*Proof.* A non-neutral cluster has `sigma_P = |F|` (regular) or `sigma_P >= 2` (in general). Lemma 3 would give
`rho > theta |F|/(4(n+1)) >= rho`, or `rho > 2 theta/(4(n+1)) >= rho`. QED.

## 2. Thick tori: corner pushes

**Pushes and their cost.** Let the faces `z` and `z'` share the edge `d`, with value `e`. The value `e` occurs once in
the boundary word of `z`, so there is a unique `e'` making `z` flat ([T] Lemma 3). Then:
- `e' = D e` (or `e D`), where `D` is conjugate to `hol(z)^(±1)`. So the change costs rank at most `sigma(hol z)`.
- Only `hol(z)` and `hol(z')` change. The new `hol(z')` is a conjugate of the old one times a conjugate of `D^(±1)`,
  so `sigma(new hol z') <= sigma(old hol z') + sigma(old hol z)`.
- Hence a push never increases the total support `sum_z sigma(hol z)` of any set of faces containing `z` and `z'`.

**Lemma 5 (neutral clusters).** Suppose `lambda_1 >= 2(n+1) theta` and every final cluster of Lemma 2 is neutral.
Then some commuting pair differs from `(b, c)` at most at `2 n (n-1) theta` sites, with total rank cost at most
`2 theta n (n-1) S`.

*Proof.* Fix a final cluster `P`, with `bb P` of lower-left cell `o` and `|P| = k`. For each `p in P` in turn, walk
from `p` left along its row to the column of `o`, then down to `o`. At each step from `z` to the next cell, push if
`z` is charged, and otherwise just move on.
- *Where the changes are.* Each path stays in `bb P` and has length at most `w + h - 2 <= 2(k-1) theta`. Every changed
  edge is interior to `bb P`, meaning both of its faces lie in `bb P`.
- *The clusters do not interact.* By Lemma 2(b), `bb P` projects injectively to `G`. By Lemma 2(c), with
  `theta >= 1`, the projected boxes of distinct clusters are disjoint and share no edge, and no box shares an edge
  with its own translates. So we may do the changes in `G` and read them in the plane periodically. The changes for
  `P` alter only the holonomies of faces of `bb P`, and no boundary edge of any box `bb P' + lambda` changes.
- *The charges move to the corner.* By induction, after the walk from `p_i` the charged cells of `bb P` lie in
  `{p_(i+1), ..., p_k} ∪ {o}`. A walk leaves every cell it leaves flat, and it absorbs any charge it meets. At the
  end only `o` can be charged.
- *The corner is flat.* The boundary word of `bb P` did not change, so it still has holonomy 1. By van Kampen
  ([R]) it is conjugate to `hol(o)`, so `hol(o) = 1`.

So every face is flat. There are at most `k (2(k-1) theta)` pushes in `bb P`. By the cost rule, each costs at most
the total support of `bb P`, which is at most `S_P = sum_(p in P) sigma(hol p)` throughout. Summing over the
clusters, using `k(k-1) <= n(n-1)` and `sum_P S_P = S`, gives at most `2 n (n-1) theta` sites and cost at most
`2 theta n (n-1) S`. QED.

## 3. Thin tori: a strip cut at every charged-row gap

Use [D] Section 2: `w = k v` is a shortest vector of `Lambda`, `l = |v|_inf`, `det(v, u) = 1`, `L = N/k`, and the row
index is `r(x) = det(v, z) mod L`. Fix the unit step `f` of [D] Lemma 4, with `det(v, f) = -l`.

**Walks.** Let `T` be `G`, or a torus `T_I` of [D] with `H >= 2l`. Let `B` be the band of the window
`{sigma_0 - l <= det(v,.) < sigma_0 - l + |v|_1}`. It has `lambda_1` faces and is a band in the sense of [R]:
for `G` by [T] (single charge on `G`), and for `T_I` by [D] Lemma 3 and the strip-case paragraph of [T]. Let a
charged face have a lift `z` of *relative height* `t = det(v, z) - sigma_0` in `[0, 2 l j]`. Walking from `z` along
`f` lowers the height by `l` per step. After `floor(t/l) + 1 <= 2j + 1` steps it lies in `[-l, 0)`, which is inside
the window since `|v|_1 >= l`. Pushing along this walk (and stopping on entering `B`) moves the charge into `B`, and
leaves every face it passes flat. So charges outside `B` are only ever at their original positions.

**Charged-row groups.** Let `r_1 < ... < r_q` be the distinct rows of charged faces (`q <= n`), and consider the
cyclic gaps `r_(i+1) - r_i mod L` (all `L` if `q = 1`). A gap is *big* if it exceeds `2l`. Let `p` be the number of
big gaps, and call the row after a big gap a *start*. From a start, the next charged rows follow at gaps of at most
`2l`, up to the next big gap. So the charged rows of a group of `k'` charges have relative heights (from their start)
in `[0, 2l(k'-1)]`. If `p = 0`, use any charged row as the start of the single group; the same bound holds.

**Lemma 6 (thin construction).** For every cover with `lambda_1 >= 2`, some commuting pair differs from `(b, c)`
at most at `3 n lambda_1 + 2 n^2` sites.

*Proof.* *Case `p <= 1`.* Let `s_0` be the start, and let `B` be the band of `G` with `sigma_0 = s_0`. Walk each
original charge into `B`, which takes at most `2n - 1` pushes each by the height bound with `j = n - 1`. All charges
then lie in `B`, and [R] Theorem 1 clears them with `lambda_1` changes. The total is at most
`lambda_1 + n (2n - 1) <= lambda_1 + 2n^2` sites.

*Case `p >= 2`.* The pieces `I_1, ..., I_p` run from each start to the row before the next start. Each piece
contains a group of `k_j` charges, of relative heights at most `2l(k_j - 1)`, followed by a big gap, so
`H_j >= 2l + 1`. Since `p >= 2`, `H_j < L`. Build the reglued pair `(b1, c1)` of [D] Section 2 and [T] (strip case):
- by [D] Lemma 2(c) it redirects `lambda_1` base moves per piece;
- on piece `j`, `(beta, gamma)` is a connection on `T_j = T_(I_j)`, and its charged faces lie in
  `(Q ∩ P_(I_j)) ∪ R_b(I_j) ∪ R_c(I_j)`. The formula for `hol1` is local, as in [T], and this uses no property of
  `Y`.

On `T_j`, take `sigma_0 = s'_j` and `B_j` the band of the window above.
- First walk the charges at the faces of `Q ∩ P_(I_j)`, each in at most `2 k_j - 1` pushes. The height bound applies
  because the lifts in `Sigma_j` have relative height in `[0, 2l(k_j - 1)]`, and heights on `T_j` are taken mod `H_j`.
- The faces still charged outside `B_j` are points of `R_b(I_j) ∪ R_c(I_j)` that no walk passed through. There are
  at most `lambda_1` of them, and by [D] Lemmas 2(d) and 4 each is one grid step from `B_j`.
- The Corollary of [R] clears piece `j` with at most `lambda_1 + lambda_1` fibre changes. The base maps stay the
  reglued ones, and the pair on `P_(I_j) x Y` commutes.

The pieces partition `G`, so the final pair commutes. The site count is
`sum_j (lambda_1 + 2 k_j n + 2 lambda_1) <= 3 p lambda_1 + 2 n^2`, and `p <= q <= n`. QED.

## 4. Proof of the theorems

**Theorem A.** The fibre is regular, so each site costs at most `|F|` and `sigma = |F|` on every charge. Lemma 1
gives `n <= 4K`, and so `K >= 1/4`. Put `theta = ceil(4(n+1) K)`.
- *If `lambda_1 >= 2(n+1) theta`.* By Corollary 4, every final cluster is neutral, and by Lemma 5,
  `dist <= 2 n^2 theta |F|`.
- *Otherwise* `lambda_1 < 2(n+1) theta`, and by Lemma 6, `dist <= (3 n lambda_1 + 2 n^2) |F| < (6 n (n+1) theta + 2 n^2) |F|`.

Now `n + 1 <= 4K + 1 <= 8K`, and `theta <= 4(n+1)K + 1 <= 32 K^2 + 1 <= 48 K^2`, using `16 K^2 >= 1`. So
- `2 n^2 theta <= 2 (16 K^2)(48 K^2) = 1536 K^4`;
- `6 n (n+1) theta + 2 n^2 <= 6 (4K)(8K)(48 K^2) + 32 K^2 <= 9216 K^4 + 512 K^4 = 9728 K^4`.

Hence `dist <= 10^4 K^4 |F| = 10^4 rho^4/|F|^3`. QED.

**Theorem B.** Lemma 1 gives `n <= 2 rho` and `S <= 4 rho`, and so `rho >= 1/2`. Put `theta = ceil(2(n+1) rho)`.
Then `n + 1 <= 2 rho + 1 <= 4 rho`, and `theta <= 8 rho^2 + 1 <= 12 rho^2`.
- *If `lambda_1 >= 2(n+1) theta`.* By Corollary 4 every final cluster is neutral, and by Lemma 5,
  `dist <= 2 theta n (n-1) S <= 2 (12 rho^2)(4 rho^2)(4 rho) = 384 rho^5`. Since `2(n+1) theta <= 96 rho^3`, this
  case includes every torus with `lambda_1 >= 96 rho^3`.
- *Otherwise*, by Lemma 6 and a cost of at most `m` per site,
  `dist < m (6 n (n+1) theta + 2 n^2) <= m (6 (2 rho)(4 rho)(12 rho^2) + 8 rho^2) <= m (576 + 32) rho^4 = 608 m rho^4`,
  using `8 rho^2 <= 32 rho^4`.

So `dist <= max(384 rho^5, 608 m rho^4) <= 608 rho^4 (rho + m)`. QED.

## 5. Remarks

- **Which step is new.** The two-charge node bounded `rho` from below case by case, depending on how the two charges
  sit. Threshold clustering is uniform in the number of charges: it chooses the scale `theta` where every cluster
  must be neutral, since otherwise `(theta+1)^2` isolating boxes give too much rank. Neutral clusters on a thick
  torus are then removed by pushes inside disjoint boxes. On a thin torus, `lambda_1 < 2(n+1) theta` is polynomial in
  `K`, so the strip cut of [D] and the rungs of [R] are cheap enough.
- **The replacement for `|F|/2`.** For general fibres the right charge weight is `sigma(hol q)/2`, the lower bound
  for `rank(P_W - I)`. It enters both sides.
  - Lower bounds: `S <= 4 rho`, and Lemma 3 with `sigma_P >= 2`.
  - Costs: the pushes of Lemma 5 change edges by conjugates of current face holonomies, and support is subadditive.

  On thick tori this makes the bound independent of `|Y|`. The factor `|Y|` enters only through the strip redirects
  and the rungs on thin tori, where Lemma 6 counts a whole fibre per site.
- **What is left for all permutation pairs.** Every pair on `d` points is a cover of the one-square torus
  (`N = 1`, `|Y| = d`), so Theorem B is only informative when `|Y|` is small. Two natural next steps:
  - make the rung closing and the strip redirects support-weighted;
  - find an equivariant map to a thick torus with small fibres, in the spirit of a Rokhlin tower for the
    `Z^2`-action.
- **Linear bounds.** The step asked for `dist = O(rho)`. The proof gives `O(K^4)`. A heuristic multi-scale `Z/2`
  configuration (a dense field of small neutral dipoles hiding larger ones) suggests that any single-scale box count
  loses a factor near `log N / log log N`. This is not proved; the question whether `F(K) = O(K)` on regular covers
  remains open.
- **Computation.** `multicharge.py` runs both constructions on 600 covers and checks every step and bound
  (`multicharge-summary.txt`). The box-count lemma was checked on 171 non-neutral clusters, each with all its
  `(theta+1)^2` boxes.
