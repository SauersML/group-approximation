---
rg: 2
id: nonabelian-two-charge-torus-covers-rank-distance-linear-proof
kind: route
target: nonabelian-two-charge-torus-covers-rank-distance-linear
requires:
  - nonabelian-band-rungs-absorb-ordered-charge-product
  - torus-dipole-covers-rank-distance-linear-in-profile
title: Box counting on free fibres, a charge push along a shortest path, and rung-closed digital bands in the strip cut give dist <= 36 rho for two-charge regular covers
---

Notation as in the claim. We cite two nodes.
- From `nonabelian-band-rungs-absorb-ordered-charge-product` (called *[R]*): Theorem 1 (rung lemma), its Corollary,
  and the van Kampen fact that the boundary holonomy of a disk of faces is a product of conjugates of its face
  holonomies.
- From `torus-dipole-covers-rank-distance-linear-in-profile-proof` (called *[D]*): Lemmas 1 to 4, which are
  statements about the lattice only.

A *site* is `(x, b)` or `(x, c)`. Changing `beta(x)`, changing `gamma(x)`, or redirecting the base move at `x`
changes one permutation on one fibre, so it costs rank at most `|F|`. A pair that differs from `(b, c)` at `M` sites
has `max(rank(b''-b), rank(c''-c)) <= |F| M`.

We assume `lambda_1 >= 2`. If `lambda_1 = 1`, then some `e_j` is in `Lambda`, the base is a cycle, and the same
proof applies with the band of one face bordering itself: [R], Theorem 1 holds verbatim for `m = 1`.

## 1. Commutators on free fibres

**Lemma 1.** Fix `s, t >= 1`. For each `x` in `G`, `[b^s, c^t]` maps the fibre over `x` to itself by left
multiplication by `W_x`. Here `W_x` is the holonomy (lifted periodically to `R^2`) of the boundary of an `s x t`
box `R_x` of faces with a fixed corner at a lift of `x`. As a result:
- `rank([b^s,c^t] - I) >= (|F|/2) #{x : W_x != 1}`;
- if the lift of `R_x` contains exactly one lift of a charged face `q`, then `W_x` is conjugate to `hol(q)^(±1)`;
- if it contains exactly the lifts of `x_0` and `x_1` inside a box `R'` that contains no other charged lift,
  then `W_x` is conjugate to `hol(∂R')^(±1)`.

*Proof.* The base maps are the commuting translations `x -> x+e1` and `x -> x+e2`, so the commutator fixes every
base point. Its fibre value is the product of the edge values along the boundary loop of `R_x`, which is `W_x`. The
map `x -> R_x` is a bijection onto boxes of that shape.

Left multiplication by `W != 1` on `F` has `|F|/ord(W)` cycles. So for a permutation matrix it has
`rank(P - I) = |F| (1 - 1/ord W) >= |F|/2`.

The other two statements are van Kampen on the disk `R_x`: only charged faces contribute. In the third case, the
flat region `R_x \ R'` makes `∂R_x` and `∂R'` freely homotopic through flat faces. QED.

**Lemma 2 (lower bounds).** Put `m_0 = min(|g|_1, lambda_1)` for two charges, and `m_0 = lambda_1` for one charge.
Let `r = ceil(m_0/2)`.
- (a) One charge: `rho >= |F| r/4 >= |F| lambda_1/8`.
- (b) Two charges: `rho >= |F| r/2 >= |F| m_0/4`.
- (c) Two charges with `|g|_1 < lambda_1`, not neutral: `rho >= |F| (p+1)^2 / (2(|g|_1 + 2 + 2p))`, where
  `p = floor((lambda_1 - 1 - |g|_1)/2)`. If also `|g|_1 < lambda_1/4`, this gives `rho >= 9 |F| lambda_1 / 256`.

*Proof.* Two faces of one `s x t` box differ by a vector of `l^1` norm at most `s + t - 2`.

(a), (b): Take `s = t = r`, so `s + t - 2 = 2r - 2 <= m_0 - 1`.
- A box contains at most one lift of any face, since `2r - 2 < lambda_1`.
- A box containing a lift of `x_0` contains no lift of `x_1`: their difference is a lift of `g`, which has `l^1`
  norm at least `|g|_1 >= m_0 > 2r - 2`.
- The `r^2` boxes containing a given lift of `x_0` have distinct corners in `G`. The same holds for `x_1`, and the
  two families are disjoint.
- Lemma 1 then gives `rank >= (|F|/2) r^2` for one charge and `>= (|F|/2) 2 r^2` for two. Divide by `2r`.

(c): Let `R_0` be the bounding box of a lift of `x_0` and the lift of `x_1` at displacement `g`. It has
`(|g_1|+1) x (|g_2|+1)` faces and contains no other charged lift, because every difference inside it has `l^1`
norm at most `|g|_1 < lambda_1`. Not neutral means `hol(∂R_0) != 1`.

Take `s = |g_1| + 1 + p` and `t = |g_2| + 1 + p`. Then `s + t - 2 = |g|_1 + 2p <= lambda_1 - 1`, so each box holds
at most one lift of each face.
- The `(p+1)^2` boxes containing `R_0` contain no charged lift except the two in `R_0`. A second lift of `x_1` would
  differ from the first by a lattice vector of norm at most `lambda_1 - 1`.
- So by Lemma 1, `W_x` is conjugate to `hol(∂R_0)^(±1) != 1` for `(p+1)^2` distinct corners. That gives
  `rank >= (|F|/2)(p+1)^2`, and `s + t = |g|_1 + 2 + 2p`.

For the numerical form, suppose `|g|_1 < lambda_1/4`.
- `p + 1 >= (lambda_1 - |g|_1)/2 > 3 lambda_1/8`.
- `s + t <= lambda_1 + 1 <= 2 lambda_1`.
- So `rho >= |F| (9/64) lambda_1^2 / (4 lambda_1) = 9 |F| lambda_1/256`. QED.

## 2. Pushing a charge

**Lemma 3 (push).** Let `y_0 = x_0, y_1, ..., y_n = x_1` be faces with `y_i` and `y_(i+1)` sharing an edge `d_i`,
and suppose every charged face is `x_0` or `x_1`. Changing the values on `d_0, ..., d_(n-1)` in turn gives a
connection whose only possibly charged face is `x_1`.

*Proof.* The value on `d_i` occurs once in the boundary word of `y_i`, so it can be chosen to make `y_i` flat.
This changes only the holonomies of `y_i` and `y_(i+1)`.

By induction, before step `i` the charged faces lie in `{y_i, x_1}`, and after it they lie in `{y_(i+1), x_1}`.
This remains true when the faces repeat, or when some `y_i = x_1`. QED.

**Lemma 4 (short dipoles).** Let `|g|_1 < lambda_1`, and push along a monotone staircase inside `R_0` (`n = |g|_1`).
- If the pair is neutral, the result is flat.
- Otherwise exactly one face, `x_1`, stays charged.

*Proof.* All the `d_i` are interior edges of `R_0`, so `hol(∂R_0)` does not change. After the push, `R_0`
contains at most one charged lift, the one of `x_1`. So `hol(x_1)` is conjugate to `hol(∂R_0)^(±1)`. QED.

**Single charge on `G` (the band exists).**
- Minkowski's theorem applied to the `l^1` ball gives `N >= lambda_1^2/2`. So `L = N/k >= k |v|_1^2/2 >= |v|_1`,
  using `lambda_1 = k|v|_1 >= 2`.
- Hence the proofs of [D], Lemmas 2(a) and 3, apply to the window `{sigma <= det(v,.) < sigma + |v|_1}` on `G`
  itself. For every `sigma`, its image is a closed cycle of `lambda_1` distinct faces.
- Consecutive faces share an edge. These edges are distinct, since consecutive steps are distinct (face, direction)
  pairs.
- The cycle has class `w`, which is primitive in `Lambda` because `Lambda ∩ Z v = Z w`.

So the image is a band in the sense of [R] with `m = lambda_1`, and choosing `sigma = det(v, z_q)` puts a given
face `q` in it. By [R], Theorem 1, one charged face costs at most `lambda_1` changes.

## 3. Proof of the theorem

If there is no charged face, then `dist = 0`.

**One charge.** By the single-charge paragraph above, `dist <= |F| lambda_1`. By Lemma 2(a), `rho >= |F| lambda_1/8`.
So `dist <= 8 rho`.

**Two charges, `|g|_1 < lambda_1`.** Here `m_0 = |g|_1`, and Lemma 2(b) gives `rho >= |F| |g|_1/4`.
- *Neutral.* By Lemma 4, `dist <= |F| |g|_1 <= 4 rho`.
- *Not neutral.* By Lemma 4, the push leaves one charge at `x_1`, and the band through `x_1` removes it. So
  `dist <= |F| (|g|_1 + lambda_1)`.
  - If `|g|_1 >= lambda_1/4`, then `|F| lambda_1 <= 4 |F| |g|_1 <= 16 rho`, so `dist <= 20 rho`.
  - Otherwise Lemma 2(c) gives `dist <= (5/4) |F| lambda_1 <= (5/4)(256/9) rho < 35.6 rho`.

**Two charges, `|g|_1 >= lambda_1`.** Here `m_0 = lambda_1`, and Lemma 2(b) gives `rho >= |F| lambda_1/4`. Use
[D] Section 2: `w = k v`, `l = |v|_inf`, the row index `r`, and the cyclic row distance `D` of the charges.

*Case `D <= 2l`.* As in [D] Section 4, using [D] Lemma 1, `|g|_1 < 3.54 lambda_1`. Push along a shortest path
(Lemma 3, `n = |g|_1`). This leaves at most one charged face, which the band through `x_1` removes. The total is
`< 4.54 lambda_1` sites, so `dist < 4.54 |F| lambda_1 < 18.2 rho`.

*Case `D >= 2l + 1` (strip cut).* Take the pieces `I_1` and `I_2` of [D] Section 4, of heights `H_j >= 2l`.
Regluing gives commuting base permutations `nb, nc` of each `P_(I_j)` ([D] Lemma 2). Put
`b1(x,a) = (nb x, beta(x) a)` and `c1(x,a) = (nc x, gamma(x) a)`.
- *The reglued charge.* `b1 c1 (x,a) = (nb nc x, beta(nc x) gamma(x) a)` and
  `c1 b1 (x,a) = (nc nb x, gamma(nb x) beta(x) a)`. So `(b1, c1)` commutes iff every
  `hol1(x) = gamma(x)^-1 beta(nc x)^-1 gamma(nb x) beta(x)` is 1.
- *A connection on each piece.* Through `phi` ([D] Lemma 2(a)), `(beta, gamma)` on `P_(I_j)` is a connection on
  the grid torus `T_(I_j) = Z^2/<w, H_j u>`, and `hol1` is its face holonomy.
- *Few new charges.* `hol1(x)` depends only on the values at `x`, `nb x` and `nc x`. So `hol1(x) = hol(x)`
  unless `x` is in `R_b ∪ R_c`. The charged set `Q` of `hol1` lies in `R_b ∪ R_c ∪ {x_0, x_1}`, so
  `|Q| <= 2 lambda_1 + 2`. This is the same set as in the abelian case, because the face formula is local.
- *All charges are next to the band.* By [D] Lemmas 2(d), 3 and 4 (the relative heights of `x_0` and `x_1` are
  `0` and `H_1 - 1`), every point of `Q ∩ P_(I_j)` lies in the digital band `B_j = B_(s'_j - l)` of `T_(I_j)` or
  shares an edge with it. `B_j` has `lambda_1` distinct faces and is a closed cycle of class `w`. The class `w` is
  primitive in `<w, H_j u>`, and the rungs are distinct as in the single-charge paragraph. Every edge of
  `T_(I_j)` borders two distinct faces, since a nonzero `a w + b H_j u` with `b != 0` has `l^1` norm at least
  `H_j/l >= 2`. So `B_j` is a band in the sense of [R].
- *Closing.* By the Corollary of [R], piece `j` becomes flat after at most `lambda_1 + |Q ∩ P_(I_j)|` fibre
  changes. The base maps `nb, nc` are untouched, and the resulting pair on `P_(I_j) x F` commutes.

The total is `2 lambda_1` redirects plus at most `2 lambda_1 + (2 lambda_1 + 2)` fibre changes, that is,
`6 lambda_1 + 2 <= 8 lambda_1` sites. So `dist <= 8 |F| lambda_1 <= 32 rho`.

Across all cases, `dist <= max(8, 4, 20, 35.6, 18.2, 32) rho < 36 rho`. QED.

## 4. Remarks

- **Where the abelian proof needed Stokes.** In [D] the tree cancellation on each piece used that the charges sum
  to 0. Here the ordered product around a piece is a commutator of the piece's holonomies. It is generally
  nontrivial, and by [R] Theorem 2 no change supported in a disk can remove it. The rung lemma pays one extra edge
  per piece. The non-neutral short case pays `lambda_1` for the same reason: a single residual charge.
- **Constants.** The constants are not sharp. On 6900 covers (`rungs-summary.txt`) the worst observed ratio is
  `dist / rho_lower <= 7.10`, where `rho_lower <= rho` is a finite maximum over boxes with `s, t <= 40`.
- **What the method does not reach.**
  - *Non-free fibres.* The only place freeness is used is Lemma 1: `rank(P - I) >= |F|/2`. For an `F`-set fibre
    `Y`, or a general permutation pair, a nontrivial holonomy may fix all but two points of the fibre. Then
    `rho` can be much smaller than `|Y|` while the site counts stay the same.
  - *Several charges.* The rung lemma removes the neutrality requirement inside a piece. What is still missing is
    a lower bound `rho >~ |F| (n lambda_1 + ...)` for `n` charges, whose clusters are not neutral in general.
