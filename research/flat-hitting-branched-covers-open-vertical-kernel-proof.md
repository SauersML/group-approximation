---
rg: 2
id: flat-hitting-branched-covers-open-vertical-kernel-proof
kind: route
title: Closed vertical slabs propagate along B-free strips, form a forest by flat hitting, and their exits inject into branch data
target: flat-hitting-branched-covers-open-vertical-kernel
requires:
  - flat-hitting-branched-covers-have-hyperbolic-pi1
  - radu-horizontal-projection-kills-delta-squared
  - radu-bmw-lattice-embeds-in-titz-witzel-kernel
---

Notation as in the target.  Imports: covering space theory, and the facts
on branched covers recorded in `sparse-branched-covers-with-sofic-pi1-give-sofic-lattice`
(each `Lk(x) -> Lk(p x)` is a covering of degree `d_x`; the vertices over a
vertex of `Y` have `sum d_x = n_X`).  The only input from
`flat-hitting-branched-covers-have-hyperbolic-pi1` is the definition of (H).
All paths are edge paths and all edges have length one.

## Step 0. Unique lifting at unbranched vertices

At an unbranched vertex `x`, `Lk(x) -> Lk(p x)` is an isomorphism.  Hence:

* **(L1)** Each edge-end of `Y` at `p(x)` has exactly one lift at `x`.  An
  edge path of `Y` lifts uniquely from `x` as long as every vertex reached,
  except possibly the last, is unbranched.
* **(L2)** Given two edge-ends at `x` spanning a corner of a square of `Y`,
  there is exactly one square of `X` with that corner at `x`.  Links of `Y`
  are simple graphs (girth at least 4), so the corner determines the square.
* **(L3)** Distinct edge-ends at `x` project to distinct edge-ends at `p x`.

Fix a vertex `o` of `Delta` over `p(y)`.  An edge path of `Delta` from `o`
projects to `Y`, and "its lift from `y`" means the lift of the projection.

## Step 1. Elements of `N` and chart independence

`H` acts freely on `Delta` by deck transformations, preserving factors.  An
element `s in N \ {1}` fixes `T1` pointwise.  If it fixed a vertex, or
inverted an edge, of `T2`, it would fix a point of `Delta`.  So `s` is
hyperbolic on `T2`, with translation length `ell(s) >= 1`, and for every
`w = (w1, w2)`

```text
d(w, s w) = d_T2(w2, s w2)   and   s w = (w1, s w2).                    (1)
```

The geodesic `[o, s o]` lies in `{o1} x T2`.  Another vertex over `p(y)` is
`h o` with `h in H`.  Then `S_L(h o) = h S_L(o) h^(-1)`, and
`p[h o, h s h^(-1) h o] = p(h[o, s o]) = p[o, s o]`.  So the set of loops in
(C), and condition (A), do not depend on the chart, since `S` is
`H`-conjugation invariant.

## Step 2. Lifting vertical strips, and propagation

Let `y in W = W^S_L(X)` with chart `o`, and let `e` be a horizontal edge-end
at `y`.  Lift `p(e)` to the edge `[o, o']` of `Delta`, so `o' = (o1', o2)`.
Take `s in S_L(o)`, put `l = d(o, s o)`, and let `o2 = t_0, ..., t_l = s o2`
be the vertices of `[o2, s o2]`.  The *strip* is the row of squares
`[o1, o1'] x [t_i, t_(i+1)]`.

**Lifting.**  Let `x_0 = y, ..., x_l` be the lift of `p[o, s o]` from `y`.
By (C) it is B-free and `x_l = y`.
* Put `f_0 = e`.
* Inductively, `Q_i` is the square of `X` given by (L2) at `x_i` with
  edge-ends `f_i` and `[x_i, x_(i+1)]`, and `f_(i+1)` is the side of `Q_i`
  opposite `f_i`.
* By induction, `f_i` projects to `p([o1, o1'] x {t_i})` and `Q_i` projects
  to `p([o1, o1'] x [t_i, t_(i+1)])`.
* Let `z_i` be the far endpoint of `f_i`.

Only the `x_i` need to be unbranched for this construction.  The strip is
*B-free* if every `z_i` is unbranched.

The edge-end `e` at `y` is **internal** if the strip is B-free for every
`s in S_L(o)`.

**Lemma 2 (propagation).**  If `e = [y, y']` is internal at `y in W`, then
`y' in W`, and the reverse edge-end at `y'` is internal.

*Proof.*
* `f_l` is the lift at `x_l = y` of `p([o1, o1'] x {s o2}) = p(s [o, o']) = p(e)`.
  By (L1), `f_l = e` and `z_l = y' = z_0`.
* The right sides of the `Q_i` form a path `z_0, ..., z_l` over
  `p[o', s o']`, since `s o' = (o1', s o2)` by (1).  All its vertices are
  unbranched, so by (L1) it is the lift of that loop from `y'`, and it
  closes.
* By (1), `S_L(o') = S_L(o)`, and `o'` is on the axis of `s` if and only if
  `o` is.  So (A) and (C) hold at `y'`.
* For the reverse edge-end and any `s`, (L2) at the unbranched `z_i`
  rebuilds the same squares `Q_i` with the two sides exchanged.  Its far
  corners are the `x_i`, which are unbranched.  QED

The **internal graph** has vertex set `W` and, as edges, the edges of `X`
both of whose ends are internal.  By Lemma 2, every internal edge-end at a
vertex of `W` belongs to an edge of this graph.

## Step 3. Flat hitting makes the internal graph a forest

**Lemma 3.**  Assume (H) with radius `R`.  Then the internal graph has no
non-backtracking edge path of length `k = 2R + 2`.  In particular it has no
cycle, loop or multiple edge, so it is a forest.

*Proof.*  Suppose `y_0, ..., y_k` is a non-backtracking internal path.
* Lift it from the chart `o` to a path `o = w^0, ..., w^k` of `Delta`.  By
  (L3) at each unbranched `y_i` this path is non-backtracking, so it is a
  geodesic of `T1` times the vertex `o2`.
* By (A) at `y_0`, choose `s in S_L(o)` with `o` on its axis.  By (1), every
  `w^i` is on the axis of `s`, and `S_L(w^i) = S_L(o)`.
* Let `F = [w^0_1, w^k_1] x [s^(-q) o2, s^q o2]`, with `q ell(s) >= 2R + 2`.
  `F` is a flat rectangle of `Delta`.

Map `F` into `X`.  On `[w^i_1, w^(i+1)_1] x [s^r o2, s^(r+1) o2]`, use the
lifted strip for `s` at the internal edge-end `[y_i, y_(i+1)]`.
* The strips at `y_(i-1)` and `y_i` agree along their common column.  By
  Lemma 2 this column is the closed loop lift from `y_i` in both.
* Consecutive translates `r, r+1` agree along their common horizontal side.
  The loop lifts close, and `f_l = f_0` (Lemma 2).

Every vertex of the image is some `x` or `z` vertex of these strips, so it is
unbranched.  At an interior vertex `u` of `F` with image `x`, the four
corners at `u` form an embedded 4-cycle in `Lk_Delta(u)`.  Their images in
`Lk(p x)`, which is covered by `Lk_Delta(u)`, form an embedded 4-cycle, since
`Delta -> Y` is a covering.  The map `Lk(x) -> Lk(p x)` is an isomorphism, so
the corners at `x` form an embedded 4-cycle as well.

So the map is a local isometry on the interior of `F`.  The interior of `F`
contains a closed Euclidean disk of radius `R`, which therefore immerses
locally isometrically into `X \ B`.  This contradicts (H).

A cycle, a loop edge or a pair of parallel edges would give non-backtracking
walks of every length.  QED

## Step 4. Exit counting gives (VS)

An **exit** is a horizontal edge-end at a vertex of `W` that is not internal.

**Lemma 4 (many exits).**  There are at least `(m - 2)|W|` exits.

*Proof.*  At an unbranched `y`, the horizontal edge-ends correspond to those
of `p(y)`, hence to the edges at `o1` in `T1`.  So there are at least `m` of
them.  A component of the forest with `c` vertices has `c - 1` edges, hence
`2(c - 1)` internal edge-ends.  It therefore has at least
`mc - 2(c-1) >= (m-2)c` exits.  Sum over components.  QED

**Lemma 5 (exits inject into branch data).**  There is an injective map
from exits to tuples `(b, epsilon, j, gamma)` where:
* `b in B`;
* `epsilon` is a horizontal edge-end at `b`;
* `0 <= j <= L`;
* `gamma` is a based closed edge path in `Y` of length at most `L`.

*Proof.*  Let `e` be an exit at `y`.  Choose `s in S_L(o)` whose strip is not
B-free.  Set `gamma = p[o, s o]`.  With the notation of Step 2, let `j` be
the least index with `z_j in B`.  Put `b = z_j`, and let `epsilon` be the end
of `f_j` at `b`.

To recover `e` from the tuple:
* `f_j` is the edge containing `epsilon`, and `x_j` is its other endpoint,
  which is unbranched.
* Lift the reverse of the initial segment `gamma[0, j]` from `x_j`.  By
  (L1) at the unbranched vertices `x_j, ..., x_1`, this gives
  `x_(j-1), ..., x_0 = y`.
* For `i = j, ..., 1`: the square `Q_(i-1)` has a corner at the unbranched
  vertex `x_i`, spanned by the edge-ends of `f_i` and `[x_(i-1), x_i]`.  By
  (L2) it is determined, and so is its opposite side `f_(i-1)`.
* This returns `f_0 = e`.  QED

The number of tuples is at most

```text
sum_{b in B} d_b D (L+1) P_L = D (L+1) P_L beta(X) n_X ,
```

since `b` has `d_b` times as many horizontal edge-ends as `p(b)`.  Combining
Lemmas 4 and 5 gives (VS).

## Step 5. Corollary 1

Let `g` be in the finite residual of `H`, let `S` be its `H`-conjugacy
class, and let `L = ell(g)`.  Choose `o` on the axis of `g`, and put `v = p(o)`.

**Finite covers close `S`.**  Let `X_0` be a finite unbranched cover of `Y`.
It corresponds to an action of `H` on a finite set, and every point
stabilizer has finite index in `H`.  The finite residual is a normal
subgroup of `H` lying in every finite-index subgroup of `H`, so it contains
every conjugate of `g` and fixes every point.  Hence at every vertex of
`X_0`, the lift of every loop `p[o', s o']` with `s in S` closes.

**Transfer.**  Let `y` be locally finite, matched with a vertex `y_0` of a
finite cover `X_0`.
* The lifts in (C) are edge paths of length at most `L` from `y`, which stay
  in the rooted `L`-ball.
* The isomorphism of balls over `Y` carries lifts to lifts, so each lift
  closes at `y` because it closes at `y_0`.
* All vertices of the ball are unbranched, so the lifts are B-free, and (C)
  holds.
* (A) holds with the chart `o` and `s = g`, whose displacement at `o` is
  `ell(g) = L`.

So `y in W^S_L(X)`, and (VS) bounds the number of locally finite vertices.

## Step 6. Corollary 2

`Y = S_R` is a VH square complex with universal cover `T_3 x T_3`.
`H = pi_1(S_R)` has index four in `Gamma_R`, which preserves the two factors
(`radu-bmw-lattice-embeds-in-titz-witzel-kernel`; `T1 = T_h`, the tree of
reduced words in `a, b, c`).  So `m = 3` and `D = 3`.

**The element.**  Some `j in {1,2,3,4}` has `(xz)^(4j) in H`: the cosets
`(xz)^(4i) H` take at most four values, and the first repeat gives the
power.  Put `g = (xz)^(4j)`.
* `g` lies in `Lambda_v = ker(Gamma_R -> Aut T_h)`, which contains `(xz)^4`
  (`radu-horizontal-projection-kills-delta-squared`).  So `g in N`.
* `(xz)^4` lies in the finite residual `Gamma_0` of `Gamma_R`
  (`radu-bmw-lattice-embeds-in-titz-witzel-kernel`, item 2), and so does `g`.
* A finite-index subgroup of `H` has finite index in `Gamma_R`, so it
  contains the normal core, which contains `Gamma_0`.  So `g` lies in the
  finite residual of `H`.
* `g != 1`.  `(xz)^4 != 1` (Titz Mite--Witzel Remark 3.6, item 2 of the same
  import), and a nontrivial element of the free group `Lambda_v` has
  nontrivial powers.

**The bound.**  Apply Corollary 1 with `L = ell(g)`, and put
`c_R = 1 / (3 (L+1) P_L)`.  If a fraction `f` of the `n_X` vertices over `v`
are locally finite, then `f n_X <= |W| <= 3 (L+1) P_L beta(X) n_X`, so
`beta(X) >= c_R f`.

**The killed constructions.**  Say `X` *agrees with a finite cover `X_0`
outside `U`*, for a vertex set `U` of `X`, if every vertex whose rooted
`L`-ball avoids `U` is unbranched and has a rooted `L`-ball isomorphic over
`Y` to one of `X_0`, with all vertices unbranched.  Such vertices over `v`
are locally finite.  If they number at least `n_X / 2`, then `f >= 1/2` and
`beta(X) >= c_R / 2`.  This bound does not depend on `R` or on the
arrangement of `U`.  QED
