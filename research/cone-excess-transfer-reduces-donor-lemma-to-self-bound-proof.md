---
rg: 2
id: cone-excess-transfer-reduces-donor-lemma-to-self-bound-proof
kind: route
target: cone-excess-transfer-reduces-donor-lemma-to-self-bound
title: Proof that transfer swaps empty free cone points and that the permutation case reduces to self-bound cone points
requires:
  - near-exact-tuples-saturate-linear-conversion-defect
artifacts:
  - experiments/cone-transfer-2026-09-17/transfer.py
  - experiments/cone-transfer-2026-09-17/fulltransfer.py
  - experiments/cone-transfer-2026-09-17/loopcopy.py
  - experiments/cone-transfer-2026-09-17/onecyl.py
  - experiments/cone-transfer-2026-09-17/swap.py
  - experiments/cone-transfer-2026-09-17/summary.txt
---

**Status: ESTABLISHED (unreviewed).** Elementary cut-and-paste on square-tiled surfaces. The only input from
elsewhere is the Lipschitz bound for `Lambda_rect` under bounded-rank changes, which is reproved in §5 in the one
line needed. The conventions are those of `experiments/cone-transfer-2026-09-17/swap.py`.

## 0. Conventions

A pair of permutations `(b, c)` of `{0, ..., d-1}` is a square-tiled surface `S`, with `d` unit squares, `b(x)` the
right neighbour and `c(x)` the up neighbour of `x`. The corners of the squares are glued into *vertices*. A vertex
with `N_v` corners has cone angle `N_v pi / 2`, and `N_v` is a positive multiple of 4. The vertex is *regular* if
`N_v = 4`, and a *cone point* otherwise.

**Excess.** Following the four corners of one square around a vertex shows that the permutation `[b, c]` (in
either composition convention) has one cycle of length `N_v / 4` for each vertex. So

`E(S) := rank([b, c] - I) = d - #cycles = sum_v (N_v / 4 - 1) = d - V(S)`.

The surface has `V` vertices, `2d` edges and `d` faces, so `E = -chi(S) = sum over components of (2g - 2)`. In
particular `E` is always even. Every cone point contributes at least 1, so the number of cone points is at most `E`.

**States and paths.** A *state* `(x, k)` is a directed grid edge with the square `x` on its left, where
`k = 0, 1, 2, 3` means the direction right, up, left, down. It leaves the corner `(x, k)` and arrives at the corner
`(x, k + 1)`. A *move* is straight, left or right. A path is a start state together with a move word `w`, and its
states are obtained by the step rule of `swap.py`:
- straight: `(x, k) -> (f_k x, k)`;
- left: `(x, k) -> (x, k + 1)`;
- right: `(x, k) -> (n_k^-1 f_k x, k - 1)`.

Here `f_k` crosses the edge at the arrival vertex that continues straight on the left side, and `n_k^-1` crosses
the next edge on that side. **Key fact (left-side locality).** Each step uses only gluings across edges that meet
the arrival vertex and lie strictly on the *left* of the path there, strictly between the incoming and the
outgoing edge.

**Rotation.** At a vertex, the outgoing states are cyclically ordered counterclockwise. Consecutive outgoing states
are exactly one corner apart, so a vertex with `N_v` corners has `N_v` outgoing states. Two outgoing states have
the same direction iff their ccw distance is a multiple of 4 ("full turns").

**Swap.** Let `P, Q` be paths with the same move word whose `2|P|` edges are pairwise distinct. The swap exchanges
the two gluings at every pair of corresponding edges: `c(y_1) <-> c(y_2)` for horizontal edges, `b(y_1) <-> b(y_2)`
for vertical ones. Geometrically, it cuts `S` along `P` and `Q` and reglues the left side of `P` to the right side
of `Q`, and the left side of `Q` to the right side of `P`. Corresponding edges have the same direction, so this is
a translation regluing.

**Cost.** The new `b'` is `b tau`, where `tau` is a product of disjoint transpositions, one for each vertical
edge pair. So `rank(b' - b) = rank(tau - I) <=` the number of vertical edges of `P`, and likewise for `c'`. The
cost is at most `|P|` in each generator.

## 1. The local swap lemma

**Lemma 1.** Let `P, Q` be paths with the same word `w` of length `L = |P|` edges, starting at the same vertex `A`
with outgoing states `s_P, s_Q` whose ccw distance at `A` is `m` corners, with `0 < m < N_A`. Write
`u_1, ..., u_(L-1)` and `u'_1, ..., u'_(L-1)` for the interior vertices of `P` and `Q`, and `B, B'` for their ends.
Assume:
- (i) the `2(L - 1)` interior vertices are pairwise distinct and differ from `A`, `B` and `B'`;
- (ii) `A` is not in `{B, B'}`.

Then the swap is defined (the `2L` edges are distinct), and the new vertex set is obtained from the old one as
follows. Every vertex off `P ∪ Q` is unchanged, and:
- (a) `A` is replaced by two vertices with `m` and `N_A - m` corners;
- (b) each pair `u_i, u'_i` is replaced by two vertices with `N_(u'_i)` and `N_(u_i)` corners (so regular
  interiors stay regular);
- (c) if `B != B'`, the two are replaced by one vertex with `N_B + N_B'` corners;
- (d) if `B = B'`, it is replaced by two vertices with `m'` and `N_B - m'` corners, where `m'` is the ccw corner
  distance at `B` between the reversed last edges of `P` and `Q`.

Hence `Delta E = 0` if `B != B'`, and `Delta E = -2` if `B = B'`.

*Proof.* **Edges are distinct.** An edge shared by `P` and `Q`, or used twice by one path, would have both
endpoints among the vertices common to the two vertex lists. By (i) and (ii), those are only `A`, and possibly
`B = B'`. No edge of `P` or `Q` joins `A` to itself: the first edge ends at `u_1 != A`, or at `B != A` when
`L = 1`. An edge from `A` to `B` used by both paths would be traversed out of `A` by both, so it would be the same
outgoing state; but `s_P != s_Q`.

**Vertices.** A vertex is a cyclic sequence of corners, and the swap changes the cyclic successor of a corner only
where the edge crossed between two consecutive corners is a swapped edge. So vertices not incident to `P ∪ Q` are
unchanged. At a vertex `z` on the paths, cut the link circle of `z` at the path edges incident to `z`. Each arc
runs from one path side to another, and after the swap it is continued across the reglued edge onto the
corresponding arc at the partner vertex.
- *(a)* At `A`, the edges of `s_P` and `s_Q` cut the link into two arcs. Going ccw from `s_P` to `s_Q`, the first arc
  starts on the left side of `P` and ends on the right side of `Q`. It has `m` corners. The swap glues exactly these
  two sides, so the arc closes into a vertex with `m` corners. The complementary arc runs from the left of `Q` to
  the right of `P`, and it closes into a vertex with `N_A - m` corners. This uses that `A` meets `P ∪ Q` only in
  the first edges: `A` is neither interior (i) nor an end (ii).
- *(b)* At `u_i`, the incoming and outgoing edges of `P` cut the link into a left arc and a right arc. By
  left-side locality, the left arc has `l = 2, 1, 3` corners for a straight move, a left turn or a right turn,
  whatever `N_(u_i)` is, and the right arc has `N_(u_i) - l`. The same move is made at `u'_i`, so its left arc also
  has `l` corners. The left arc of `u_i` is glued at both of its ends to the right arc of `u'_i`, which gives
  `l + (N_(u'_i) - l) = N_(u'_i)` corners. Symmetrically, the right arc of `u_i` joins the left arc of `u'_i`, which
  gives `N_(u_i)`. By (i), no other path edge meets `u_i` or `u'_i`.
- *(c)* At `B`, the last edge of `P` cuts the link into one arc, running from the right side of `P` ccw round to the
  left side of `P`. At `B'`, there is one arc from the right of `Q` to the left of `Q`. The regluing joins the left
  of `P` to the right of `Q`, and the left of `Q` to the right of `P`. So the two arcs form one cycle with
  `N_B + N_B'` corners.
- *(d)* If `B = B'`, the two last edges cut the link into two arcs. One runs from the right of `P` to the left of
  `Q`, and the other from the right of `Q` to the left of `P`. Each closes on itself, with `m'` and `N_B - m'`
  corners.

**Excess.** `E = d - V`, and `d` is unchanged. In case (c), `V` changes by `+1 - 1 = 0`. In case (d), it changes
by `+1 + 1 = +2`. □

**Theorem A** is Lemma 1 with `m = 4`, `N_A = 4(k + 1)` and `B != B'`. The vertex `A` splits into a regular vertex
and one with `4k` corners, and `B, B'` merge, so the excess is unchanged. `transfer.py` recomputes the full
vertex multiset after each admissible swap and compares it with (a) to (c). It matched in 60 422 of 60 422 cases.

## 2. The full transfer (Theorem A')

Let `N_A = 4(k + 1)`, and let `s_0, ..., s_k` be the outgoing states at `A` with `s_j` at ccw corner distance `4j`
from `s_0`. Let `P_j` be the path from `s_j` with a fixed word `w`. Assume:
- (i') the interior vertices of all the `P_j` are pairwise distinct, and differ from `A` and from every end;
- (ii') no end is `A`.

Let `S_0 = S`, and let `S_j` be `S_(j-1)` with `P_(j-1)` swapped against `P_j`, where the paths are always recomputed
in the current surface from the same start states with the same word.

**Lemma 2 (path invariance).** In every `S_j`, each `P_i` has the same sequence of states as in `S`, so each state
has the same square on its left.

*Proof.* By induction on `j`. The states of `P_i` are computed by steps at its interior vertices. By left-side
locality, those steps use only gluings across edges that meet an interior vertex `z` of `P_i` strictly on the left
of `P_i`. Such an edge is not an edge of `P_i`, because `z` is visited once. It is also not an edge of any other
`P_l`: every edge of `P_l` has both endpoints among `A`, the interior vertices of `P_l` and the ends, and by (i')
`z` is none of these. The swap producing `S_j` changes only gluings across edges of `P_(j-1)` and `P_j`, so the
steps of `P_i` are unchanged. (The vertex classes are regrouped by a swap, but (i') is preserved: by Lemma 1(b)
each new interior vertex is made of arcs of exactly two old interior vertices of the swapped pair. The ends and the
pieces of `A` are made only of end corners and `A`-corners respectively, by Lemma 1(a), (c), (d).) □

**Induction.** Suppose that in `S_(j-1)` the corners of `A` that lie at ccw positions `>= 4(j - 1)` from `s_0` form
one vertex `A_(j-1)` with `4(k - j + 2)` corners, in their original ccw order, and that the other corners of `A`
lie in regular vertices. For `j = 1` this is the hypothesis.

Lemma 1 applies to `P_(j-1), P_j` in `S_(j-1)`. They start at `A_(j-1)` with ccw distance `m = 4`, and (i), (ii)
follow from (i'), (ii') and the remark in the proof of Lemma 2. By Lemma 1(a), `A_(j-1)` splits into the arc from
`s_(j-1)` to `s_j`, which has 4 corners and is regular, and `A_j`, which has `4(k - j + 1)` corners in the same
cyclic order and contains `s_j, ..., s_k` spaced 4 apart. So the induction continues, and after `j = k` every
corner of `A` lies in a regular vertex.

**Excess.** By Lemma 1, the `j`-th swap changes `E` by 0, or by -2 exactly when the current ends of `P_(j-1)` and
`P_j` are the same vertex of `S_(j-1)`. Suppose no swap is a -2 swap. Then by Lemma 1(c) the current end of `P_j`
after swap `j` is the union of the old end vertices of `P_0, ..., P_j`, which must have been distinct: a repeat
`B_j` would already have been part of the current end of `P_(j-1)`, which forces a -2 swap. So at the end the
ends form one vertex `W` with `sum_j N_(B_j)` corners. Its excess is `sum_j (N_(B_j)/4) - 1 = k + sum_j e(B_j)`,
where `e(v) = N_v/4 - 1`.

**Cost.** There are `k` swaps, each costing at most `|w| + 1 = |P_0|` in each generator. Rank is subadditive, so
the chain costs at most `k |P_0|` in each generator. □

`fulltransfer.py` ran this chain on 40 232 families (seeds 2 and 4, all words of length at most 5, every rotation
class `r_0` of start states at every cone point). Every one of the 41 451 swaps had the change predicted from the
coincidence of current ends, and `A` ended with all corners regular in every family. In an earlier variant that
swapped `P_0` against every `P_j`, the excess rose by 2 in 347 steps. Once `s_0` sits in a regular piece, `P_0` no
longer starts at the vertex of `P_j`, so Lemma 1 does not apply to that pair.

## 3. The cone-ball dichotomy (Theorem B)

**Model.** Let `C` be the square-tiled cone of angle `2 pi (k + 1)`, the `(k + 1)`-fold cyclic cover of the unit
square tiling of `R^2` branched at `0`. Write `pos` for the covering projection, `R` for the deck rotation by
`2 pi`, and `|v|_inf = |pos(v)|_inf`. `R` acts freely on everything except the apex `o`. `C` is the union of
`4(k + 1)` closed quadrant sectors, each mapped isometrically by `pos` onto a closed quadrant. `Bbar_r` is the set of
squares of `C` whose corners have `|.|_inf <= r`. Match the `4(k + 1)` corners at `o` with the corners of `A` in
ccw order.

**Developing map.** Follow each ray from `o` in `C` by the geodesic in `S` that leaves `A` at the matching angle.
Let `t_c` be the least `l^inf` radius at which some such geodesic reaches a cone point of `S`, `A` included, at
positive time, with `t_c = infinity` if none does. Rays meet vertices only at lattice points, so `t_c` is a
positive integer or `infinity`. Then `D := exp_A` is a local isometry of the open ball `U_(t_c)`. It extends
continuously to the closed ball of any finite radius `r <= t_c`. It maps lattice points to vertices and squares of
`Bbar_r` to squares, and it respects adjacency across any edge shared by two squares of `Bbar_r`, since the
interior of such an edge lies in the open ball. Hence:

- (D1) for every model path of states whose left-side squares at its interior vertices lie in `Bbar_r`, the path in
  `S` from the matching state with the same word has `i`-th vertex `D(u_i)`;
- (D2) `D` commutes with `b^(+-1)` and `c^(+-1)` on pairs of adjacent squares of `Bbar_r`.

**Good radii.** For an integer `r <= t_c`, say `Inj(r)` holds if no non-apex lattice point of `Bbar_r` develops to
`A`, and `D` is injective on the non-apex lattice points of `Bbar_r`. Let `r*` be the least integer `r >= 1` such
that `r = t_c` or `Inj(r)` fails. It is finite, because `S` is finite. By construction:
- every non-apex lattice point `u` with `|u|_inf < r*` develops to a regular vertex;
- `Inj(m)` holds for every `m < r*`.

**Lemma 3 (injectivity on squares).** If `Inj(m)` holds and `m < t_c`, then `D` is injective on the squares of
`Bbar_m`.

*Proof.* Let `sigma != sigma'` have the same image, and let `l, l'` be their lower-left corners, so
`D(l) = D(l')`.
- If `l = l' = o`, the two squares carry distinct lower-left corners at `o`. These match distinct corners of `A`,
  and a square has only one lower-left corner.
- If `l = l' != o`, then `sigma = sigma'`.
- If exactly one of `l, l'` is `o`, the other develops to `A`.
- If `l != l'` and neither is `o`, injectivity fails. □

**Lemma 4 (rectangle count).** If `1 <= m < r*`, then `rank([b^m, c^m] - I) >= (k + 1) m^2 / 2`. Consequently
`(k + 1) m^2 / 2 <= 2 rho m`, so `m <= 4 rho / (k + 1) <= 2 rho`, and `r* <= 2 rho + 1`.

*Proof.* Take a model square `x` with lower-left corner at plane position `(p, q)`, where `p, q` lie in
`{-m, ..., -1}`. There are `(k + 1) m^2` such squares. The box of squares with lower-left corners in
`[p, p + m] x [q, q + m]` has all its corners in `[-m, m]^2`, so it lies in `Bbar_m`. Follow the dual path "right
`m`, then up `m`" and the path "up `m`, then right `m`" from `x`, and call the model end squares `y_1` and `y_2`.
They lie over the same plane square. The loop formed by the first path and the reverse of the second encloses the
lattice points `(i, j)` with `p < i <= p + m` and `q < j <= q + m`, and `(0, 0)` is among them. So it winds once
around `o`, and `y_2 = R^(+-1) y_1 != y_1`. By (D2), in `S` we get `(c^m b^m)(D x) = D(y_1)` and
`(b^m c^m)(D x) = D(y_2)`. These differ by Lemma 3 (`m < r* <= t_c`). The squares `D x` are pairwise distinct,
also by Lemma 3.

So the permutation `(b^m c^m)^-1 (c^m b^m)` moves at least `(k + 1) m^2` points. For a permutation `pi`,
`rank(pi - I) = sum over cycles of (length - 1) >= #moved / 2`. Also
`rank(XY - YX) = rank(X Y X^-1 Y^-1 - I)`, whatever the order. Hence
`rank([b^m, c^m] - I) >= (k + 1) m^2 / 2`, while the profile gives `<= rho (m + m)`. Apply this with
`m = r* - 1`. □

**Staircases.** For a non-apex lattice point `v`, let `st(v)` be the model path that lies in a closed quadrant
sector containing `v`. With coordinates in that sector in which `pos(v) = (p, q)` and `p, q >= 0`, it goes `p` steps
along the first boundary ray and then `q` steps parallel to the second. Its length is `|v|_1 = p + q`, its interior
lattice points `u` satisfy `|u|_inf <= |v|_inf` and `|u|_1 < |v|_1`, and none of them is `o`. Its left-side squares
lie in the box `[0, p] x [0, q]`, or in the unit strip along the ray when `p = 0` or `q = 0`, so they lie in
`Bbar_(|v|_inf)`. So (D1) applies to `st(v)` whenever `|v|_inf <= r*`. Its developed path runs from `A` to `D(v)`
and has holonomy `pos(v)`. For each `j`, `R^j st(v) = st(R^j v)` has the same word, and its start state at `o` is
`4j` corners ccw from that of `st(v)`.

**The dichotomy at `r*`.** Say `A` is *self-bound* if either
- (S1) some non-apex lattice point `v` of `Bbar_(r*)` has `D(v) = A`, or
- (S2) two distinct non-apex lattice points `v, v'` of `Bbar_(r*)` have the same *regular* image.

Otherwise `A` is *free*. A free `A` has `r* = t_c`. Indeed, if `r* < t_c`, then `Inj(r*)` fails while every non-apex
lattice point of `Bbar_(r*)` has a regular image, and that is (S2). A ray then reaches a cone point at a lattice
point of radius `t_c = r*`, and this cone point is not `A`, by the failure of (S1).

*Self-bound case.*
- In (S1), the developed `st(v)` is a closed edge path at `A` of length `|v|_1 <= 2 r*` with holonomy
  `pos(v) != 0`.
- In (S2), the developed `st(v)`, followed by the reverse of the developed `st(v')`, is a closed edge path at `A`
  of length at most `4 r* <= 8 rho + 4`, with holonomy `pos(v) - pos(v')`.

This holonomy is nonzero. Suppose instead `pos(v) = pos(v')`, so that `v' = R^j v` with `j != 0`. Let `g, g'` be the
straight model segments from `o` to `v` and `v'`. Lattice points strictly inside them have `|.|_inf < |v|_inf <= r*`,
so they develop to regular vertices. The whole open segments develop to paths through regular points. Reversed, the
developed segments are two geodesics from the regular point `D(v) = D(v')`, in the same direction `-pos(v)` and of
the same length, through regular points. A geodesic from a regular point in a given direction is unique until it
meets a cone point, so the two coincide. They therefore reach `A` with the same germ, that is, at the same angle in
`[0, 2 pi (k + 1))`. `D` is an isometry near `o`, so `g = g'` and `v = v'`, which is a contradiction.

*Free case.* Let `v` minimise `|.|_1` among the lattice points of `Bbar_(r*)` with a cone-point image. Its image is
not `A`. Put `P_j := D(st(R^j v))` for `j = 0, ..., k`. These are `k + 1` paths with one word, from start states one
full turn apart at `A`, of length `|v|_1 <= 2 r*`. We check the hypotheses of §2.
- The interior points `R^j u` all have `|.|_1 < |v|_1`, so by minimality they have regular images.
- They are pairwise distinct model points, since `R` acts freely off `o` and the `u` on one staircase have distinct
  positions. By the failure of (S2), their images are pairwise distinct.
- An interior image equal to an end image `D(R^j v)` would be regular. The two model points are distinct, since
  their `|.|_1` differ, so this again contradicts the failure of (S2).
- No image is `A`, by the failure of (S1).

So (i') and (ii') hold. By §2, the chain either lowers `E` by 2, or keeps `E`. In the second case `A` becomes
regular, the ends merge into one vertex `W`, the interior vertices keep their corner counts (Lemma 1(b)), and all
other vertices are unchanged. The cone points of the new surface are the old ones, minus `A`, minus the cone
points among the ends (at least `D(v)`), plus `W`. So their number drops by at least 1. □

If `A` is the only cone point, the free case is impossible, since it needs a cone point `C != A`.

## 4. Lipschitz bound

**Lemma 5.** If `rank(b' - b) <= q` and `rank(c' - c) <= q`, then `Lambda_rect(b', c') <= Lambda_rect(b, c) + 2q`.
Padding both by a commuting pair changes neither side.

*Proof.* `b'^s - b^s` is a sum of `s` terms, each containing the factor `b' - b`, so it has rank at most `sq`.
Likewise `b'^-s - b^-s = b'^-s (b^s - b'^s) b^-s` has rank at most `sq`. Replacing the four factors of
`[b^s, c^t]` one at a time changes it by rank at most `2sq + 2tq`. So
`rank([b'^s, c'^t] - I) <= rank([b^s, c^t] - I) + 2q(s + t)`. Divide by `s + t`. A commuting padding block adds a
block equal to `I` to every commutator. (This is the elementary half of Lemma B of
`near-exact-tuples-saturate-linear-conversion-defect-proof`.) □

## 5. The reduction (Corollary C)

**Self-bound lemma (hypothesis).** There is a nondecreasing function `P` with the following property. For every
permutation pair with profile at most `rho` and a self-bound cone point, after padding by a flat torus, some chain
of swaps costing at most `P(rho)` in each generator lowers `E`.

**Corollary C.** Assume the self-bound lemma. Let `(b, c)` be a permutation pair with `Lambda_rect(b, c) <= K`.
Then after padding it is within rank `F(K)` of a commuting pair, in each generator. Here
`F(K) = sum_(i < N) c(rho_i)`, with `rho_0 = K`, `c(rho) = max(2K(4 rho + 2), P(rho))`,
`rho_(i+1) = rho_i + 2 c(rho_i)` and `N = K(2K + 1)`.

*Proof.* Run the following loop while `E > 0`:
- if some cone point is free, do the full transfer of Theorem B at it;
- otherwise every cone point is self-bound, and we apply the self-bound lemma at one of them.

Let `E_0 = rank([b, c] - I) <= 2K`, which is the profile at `s = t = 1`.

**Progress.** Every step either lowers `E`, by at least 2 since `E` is even, or keeps `E` and lowers the number of
cone points. The number of cone points is at most `E <= E_0`. So there are at most `E_0 / 2` phases between drops
of `E`, and each phase has at most `E_0` neutral steps and one lowering step. The number of steps is at most
`(E_0 / 2)(E_0 + 1) <= K(2K + 1) = N`.

**Cost.** Let `rho_i` bound the profile before step `i`. A full transfer at a cone point of excess `k <= E_0` uses
`k` swaps of length at most `2 r* <= 4 rho_i + 2` (Theorems A' and B). So it costs at most
`E_0 (4 rho_i + 2) <= 2K(4 rho_i + 2)` in each generator. A self-bound step costs at most `P(rho_i)`. In both
cases the cost is at most `c(rho_i)`, and by Lemma 5 the profile after the step is at most `rho_i + 2 c(rho_i)`.
Since `c` is nondecreasing, these bounds propagate by induction.

**End.** When `E = 0`, `[b, c] = I`, so the current pair (with its padding) commutes. Rank distance is subadditive
along the steps, and padding blocks are commuting flat tori. So the final commuting pair is within `sum_i c(rho_i)`
of `(b, c) (+)` padding, in each generator. □

**Size of `F`.** Even for polynomial `P`, `F` is a `K(2K + 1)`-fold iterate. With `P` linear, `rho_i` grows
geometrically by a factor of about `16K`, so `F(K) = exp(O(K^2 log K))`. It is a function of `K` alone, as the
target requires. It is not polynomial, and a polynomial bound would need the transfers to avoid raising the
profile.

## 6. Neutral loop-copy moves, and what is left

`loopcopy.py` swapped a loop `P_0` at `A` (the path returns to `A`) with its rotated copy `P_j`, which ends at
`B_j != A`. This is outside Lemma 1, because the end of `P_0` is `A`. In all 767 cases `E` was unchanged, and the
corner multiset shows only a redistribution of excess between `A` and `B_j`. Such a move is neutral. It can feed a
later transfer or handle, but it never lowers `E` by itself.

**The remaining step.** Theorem B and Corollary C reduce the donor slit-pair lemma for permutation pairs to
self-bound cone points. Such a point carries a closed edge path at `A` of nonzero holonomy `u` and length at most
`8 rho + 4`, and no other cone point at smaller `l^inf` radius. The known hard cases are all self-bound. Each has
exactly one cone point, of angle `6 pi` (`E = 2`), and a lone cone point is self-bound; this was checked for
`n = 4, 5, 8` and the blocks `(8, 2, 2)` and `(9, 3, 3)`.
- In the excised square of `excised-square-kills-cone-local-slit-pair-repair`, every cone-local repair costs at
  least `n/4 - 1/2`.
- In the blocks of `lattice-donor-excises-sign-matched-cone-handles`, the sign-matched donor handle is the
  lowering chain.

**Proposition 7 (handles alone do not suffice).** Take `C >= 3` and `H >= 1`. Let `sigma` be a permutation of
`{0, ..., C-1}` for which the one-cylinder surface below has a single cone point `A`, of angle `6 pi`; `onecyl.py`
finds `sigma = (0, 2, 1)` for `C = 3` and `(0, 1, 3, 2)` for `C = 4`. The squares are `(i, r)` with `0 <= i < C` and
`0 <= r < H`, and:
- `b(i, r) = (i + 1 mod C, r)`;
- `c(i, r) = (i, r + 1)` for `r < H - 1`, and `c(i, H - 1) = (sigma(i), 0)`.

Then:
- (a) `Lambda_rect <= C` for every `H`;
- (b) `A` is self-bound, and every sign-matched handle at `A` has length at least `H`;
- (c) a one-edge same-vertex slit pair lowers `E` from 2 to 0.

So, at bounded profile, the handle alternative of the donor lemma cannot stand alone.

*Proof.*
- **(a)** `b^s` preserves rows, and `c^t` moves a square up `t` rows, applying `sigma` at each seam crossing. The
  number of crossings depends only on `r` and `t`. So `(c^t b^s)(i, r) = (b^s c^t)(i, r)` unless `r + t >= H`.
  That leaves at most `C min(t, H) <= C(s + t)` moved points, and `rank(pi - I) <= #moved`.
- **(b)** The vertex structure off the seam is regular for every `H`, so `A` is the only cone point, and a lone cone
  point is self-bound (§3). The row index `r mod H` is a well-defined function on `S` that changes by exactly
  `+-1` along each vertical edge. So every closed edge path has vertical holonomy in `H Z`, and a loop with
  `det(u, w) != 0` against another loop has length at least `H`.
- **(c)** Verified by `best_swap` for `C = 3, 4` and `H` up to 16: a pair of seam edges at `A`, with cost `(0, 1)`,
  gives `E = 0`. □

Together with `excised-square-kills-cone-local-slit-pair-repair`, where cone-local slit pairs cost at least
`n/4 - 1/2` but a donor handle of length at most 8 works, this shows that both alternatives of the donor lemma are
needed at self-bound points.

What is needed is a second loop `beta` at `A` with holonomy `w` that crosses `u` at `A` with the sign of
`det(u, w)` (hypothesis (H1) there) and has simple donor copies (H2), at length `poly(rho)`. Otherwise, a family of
self-bound points where no such `beta` exists would refute the lemma. The developed ball supplies only the one short
loop, so the candidate for `beta` is a second failure of injectivity found by continuing the development past
`r*` inside the complement of the first loop.
