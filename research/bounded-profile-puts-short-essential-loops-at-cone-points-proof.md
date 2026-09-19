---
rg: 2
id: bounded-profile-puts-short-essential-loops-at-cone-points-proof
kind: route
target: bounded-profile-puts-short-essential-loops-at-cone-points
title: Proof that a bounded rectangle profile puts a short essential loop at every cone point, via CAT(0) universal covers of square-tiled surfaces and the Flat Quadrilateral Theorem
requires:
  - near-exact-tuples-saturate-linear-conversion-defect
  - one-row-profile-pairs-need-arc-tori-not-rotations
---

Throughout, `b` and `c` are permutations of a finite set `X`, identified with their permutation matrices. Words are
applied right to left, so `w = c^-t b^-s c^t b^s` applies `b^s` first. For a permutation `g`,
`rank(g - I) = |X| - cyc(g)`. A cycle of length `l >= 2` contributes `l - 1`, which lies in `[l/2, l)`, so

  (R) `moved(g) / 2 <= rank(g - I) <= moved(g)`, where `moved(g) = #{x : g(x) != x}`.

This is (R) of `one-row-profile-pairs-need-arc-tori-not-rotations-proof`. The word `w` above equals `[u^-1, v^-1]` for
`u = c^t`, `v = b^s`. Conjugating by `vu` turns it into `[u, v] = [c^t, b^s] = [b^s, c^t]^-1`. So
`rank(w - I) = rank([b^s, c^t] - I)`.

**Step 0 (the surface).** Let `S = S(b, c)` be the square complex with one closed unit square `Q_x` for each `x` in `X`.
The right side of `Q_x` is glued to the left side of `Q_(b x)`, and the top of `Q_x` to the bottom of `Q_(c x)`, all by
translations. Four squares meet at the upper-right corner of `Q_x`. Walking counterclockwise, we pass through
`Q_x`, `Q_(b x)`, `Q_(c b x)` and `Q_(b^-1 c b x)`, and then return to `Q_k(x)`, where `k = c^-1 b^-1 c b`. So the
vertices correspond to the cycles of `k`, and a vertex whose `k`-cycle has length `m` has cone angle `2 pi m`. A vertex
is a *cone point* if `m >= 2`.

For a one-row pair (`b = +1` on `Z/n`), `k(x) = x` exactly when `c(x+1) = c(x) + 1`. So the cone points are exactly the
upper-right corners of the squares in the break set `B_1 = {x : c(x+1) != c(x) + 1}`.

`S` is a closed oriented surface, possibly disconnected, with a flat metric whose cone angles lie in
`2 pi Z_(>= 1)`. Its components have genus at least 1: Gauss-Bonnet gives `2 - 2g = -sum (m_v - 1) <= 0`.

**Step 1 (CAT(0) facts).** Fix a component `S_0` and its universal cover `p: S~ -> S_0`, with the lifted length metric
and square structure.
- (F1) `S~` is CAT(0). It is a complete geodesic polyhedral 2-complex. The link of every vertex is a circle of length
  equal to the cone angle, which is at least `2 pi`, so `S~` is locally CAT(0) (Bridson-Haefliger II.5.2 and the link condition II.5.5-5.6).
  It is simply connected, so it is CAT(0) by Cartan-Hadamard (II.4.1).
- (F2) All gluings are translations, so there is a *developing map* `dev: S~ -> R^2`. It is a translation on each square
  and a local isometry at every regular point. The *period* of a closed curve `l` in `S` is `dev(end) - dev(start)` of
  any lift. It is a homotopy invariant, so a closed curve with nonzero period is homotopically nontrivial.
- (F3) Take `s` consecutive squares `Q_x, Q_(b x), ..., Q_(b^(s-1) x)`. The path through their centres is a straight
  segment of length `s - 1` that avoids the vertices, so it is a local geodesic, and hence a geodesic in `S~`
  (II.1.4(2)). The same holds vertically.

**Lemma 1 (flat or essential).** Let `s, t >= 1` and let `y` in `X` satisfy `w(y) = y`. Let `l` be the closed curve
through the centres that starts at `Q_y` and moves right `s`, up `t`, left `s` and down `t` squares.
- If `l` is null-homotopic, then no vertex of `S` in the set `V(y, s, t)` is a cone point. Here `V(y, s, t)` is the set
  of upper-right corners of the squares `b^a c^b y` with `0 <= a <= s - 1` and `0 <= b <= t - 1`.
- The period of `l` is always `0`.

*Proof.* The period is `(s, 0) + (0, t) + (-s, 0) + (0, -t) = 0`. Suppose `l` is null-homotopic. Then its lift `l~` at a
lift `y~` of `Q_y` is closed. By (F3), `l~` is a geodesic quadrilateral in the CAT(0) space `S~`. Its four vertices
are centres of squares, which are regular points with flat neighbourhoods. At each vertex the two sides leave in
orthogonal directions, so the Alexandrov angle there is `pi/2`, and the four angles sum to `2 pi`. By the Flat
Quadrilateral Theorem (II.2.11), the convex hull `F` of `l~` is isometric to a convex Euclidean quadrilateral. Its sides
have lengths `s, t, s, t` and its angles are right angles, so `F` is a rectangle.
- In the developing coordinates with `Q_(y~) = [0, 1]^2`, `dev` maps `F` isometrically onto
  `[1/2, s + 1/2] x [1/2, t + 1/2]`.
- Fix `(a, b)` in the given ranges and let `z~` be the endpoint of the path from `y~` that goes up `b` squares and then
  right `a` squares. This path runs along the boundary of `F` and then inside it. By (F2), `z~` is the square of `S~`
  whose centre has `dev = (a + 1/2, b + 1/2)`, and `z~` projects to `Q_(b^a c^b y)`.
- The segment from that centre to `dev = (a + 1, b + 1)` is a diagonal of `z~`. It lies in `F`, and its endpoint is the
  upper-right corner of `z~`. Since `1 <= a + 1 <= s` and `1 <= b + 1 <= t`, that corner is in the interior of `F`.
- The interior of `F` is flat, so every point in it has total angle `2 pi`. Therefore that corner is regular.
[]

**Theorem 2 (short-loop dichotomy).** Let `K >= 0` with `rank([b^R, c^R] - I) <= 2 K R`, where `R = floor(4K) + 1`
(this holds whenever `Lambda_rect(b, c) <= K`). Let `v` be a cone point, and let `x` be a square whose upper-right
corner is `v`. For `0 <= i, j < R`, put `y_ij = c^-j b^-i x`. Then at least one of the following holds.
- (a) Some `y_ij` is fixed by `w = c^-R b^-R c^R b^R`, and its rectangle loop, of side `R` and period `0`, is
  homotopically nontrivial.
- (b) `y_ij = y_i'j'` for some `(i, j) != (i', j')`. Then the closed curve at `Q_x` that goes left `i`, down `j`, up `j'`
  and right `i'` has length at most `4(R - 1)` and period `(i' - i, j' - j) != 0`, so it is homotopically nontrivial.

In both cases the curve lies in the metric ball of radius `4R` about `v`.

*Proof.* Suppose (b) fails. Then the `R^2` squares `y_ij` are distinct. By (R) and the hypothesis,
`moved(w) <= 2 rank(w - I) <= 4 K R`, which is less than `R^2` because `R > 4K`. So some `y = y_ij` is fixed by `w`. The
vertex `v` is the upper-right corner of `x = b^i c^j y`, with `0 <= i, j <= R - 1`, so `v` is in `V(y, R, R)`. Since `v`
is a cone point, Lemma 1 says that the loop is not null-homotopic, which is (a).

In case (b), the period is `dev` of the endpoint minus `dev` of the start of the lifted path, which is
`(-i, -j) + (i', j')`, and this is nonzero. The distance bound holds because every square named here is within `R`
steps of `x` in each coordinate. []

**Corollary 3 (quadratic profile below the local systole).** Let `v` be a cone point and `R >= 1`. Suppose every closed
curve of length at most `4R` in the ball `B(v, 4R)` is null-homotopic. Then all `R^2` squares `y_ij` are moved by `w`,
so `rank([b^R, c^R] - I) >= R^2 / 2` and `Lambda_rect(b, c) >= R / 4`.

*Proof.* Case (b) cannot occur, so the `y_ij` are distinct. If `y_ij` were fixed by `w`, Lemma 1 would give a contradiction, as in the proof of Theorem 2. Then
apply (R). []

**Scope.**
- Lemma 1, Theorem 2 and Corollary 3 hold for all permutation pairs, not only one-row pairs.
- In the one-row case they place a short essential loop within lattice distance `R = O(K)` of every square of `B_1`,
  that is, in the union of `b^i c^j (B_1)` over `|i|, |j| <= R`. This proves the localisation half of the step proposed
  in the brief, with the `b`-fattening that the step needs.
- The converse half (a short essential loop at every cone point implies an `(F(K), F(K))`-arc-torus) is proved here
  only through explicit repairs of individual examples, such as the 157 example, and otherwise it is supported by computation (see the claim). It is not proved in general.
- `near-exact-tuples-saturate-linear-conversion-defect` provides the converse inequality (distance `delta` gives profile
  at most `2 delta`). Together with Corollary 3 it shows that every pair within distance `delta` of a commuting pair has
  local systole `O(delta)` at every cone point.
