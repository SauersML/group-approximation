---
rg: 2
id: fpbs-superset-pu-certificate-fails-on-237-triangle-group-proof
kind: route
title: Planar duality with a heptagon-and-triangles dual, and a detour-weighted walk count on the triangle-and-14-gon tiling
target: fpbs-superset-pu-certificate-fails-on-237-triangle-group
requires:
  - fpbs-bs-planar-transitive-dual-threshold-identity
artifacts:
  - experiments/fpbs-superset-pu-certificate-2026-09-17/check.py
  - experiments/fpbs-superset-pu-certificate-2026-09-17/output.txt
---

Notation: `Delta = <x, y | x^2, y^3, (xy)^7>`, `S = {x, y, y^-1}`,
`T = S ∪ {xy, (xy)^-1}`, `G_S = Cay(Delta,S)`, `G_T = Cay(Delta,T)`. Write
`Y = y^-1`.

## 0. Classical input on Delta

Delta is the orientation-preserving subgroup of the reflection group of the
tiling of `H^2` by the `(pi/2, pi/3, pi/7)` Schwarz triangle. Here `x`, `y`
and `xy` act as rotations by `pi`, `2pi/3` and `2pi/7` about the three
vertices of one triangle, and the action is properly discontinuous and
cocompact. This is Poincare's polygon theorem. See, for instance,
W. Magnus, *Noneuclidean Tesselations and Their Groups* (1974), Ch. II, or
S. Katok, *Fuchsian Groups* (1992), Sec. 4.3. Only the following consequences
are used.

- (D1) `x`, `y`, `xy` have orders exactly 2, 3, 7, and `Delta` is infinite.
- (D2) `x ∉ <xy>`. If `x` were a power of `xy`, then `y = x^-1 (xy)` would be
  too, and `Delta = <xy>` would have order 7, contradicting (D1).
- (D3) By Svarc--Milnor every Cayley graph of `Delta` is quasi-isometric to
  `H^2`. So it is nonamenable, by the quotation "A graph quasi-isometric with
  H2 must be nonamenable" in the cited route of
  `fpbs-bs-planar-transitive-dual-threshold-identity`. It is also one-ended,
  since the number of ends is a quasi-isometry invariant and `H^2` has one end.

**Simplicity.** Both Cayley graphs are simple.
- For `G_S`: `x ≠ y^±1`, and `y ≠ Y` since `y` has order 3.
- For `G_T`: `xy ∉ {e, x, y, Y}`. Indeed, `xy = x` forces `y = e`; `xy = y`
  forces `x = e`; and `xy = Y` forces `x = y^-2 = y`, which contradicts the
  orders.
- Also `xy ≠ (xy)^-1`, since `xy` has order 7.

## 1. G_S is the 3.14.14 tiling of the plane

Start from the Cayley 2-complex of the presentation, which is simply connected.
Change it in two ways.
- Collapse each `x`-digon `g -> gx -> g` onto one undirected edge
  `{g, gx}`.
- Keep one 2-cell per coset `g<y>` and one per coset `g<xy>`, deleting the
  other copies. The deleted copies have the same attaching loops, up to
  rotation, so the normal closure of the attaching loops in the fundamental
  group of the 1-skeleton does not change.

The result `K` is a simply connected 2-complex whose 1-skeleton is `G_S`. Its
2-cells are:
- the triangles `g<y>`, with boundary `g, gy, gy^2`;
- the 14-gons `F_g = g<xy>`, with boundary cycle
  `g, gx, gxy, gxyx, ..., g(xy)^6 x, g`, i.e. the vertices `g(xy)^k` and
  `g(xy)^k x` for `k mod 7`.

These boundaries are embedded cycles. For triangles this follows from (D1).
For 14-gons, the elements `g(xy)^k` are distinct by (D1), the elements
`g(xy)^k x` are distinct by (D1), and `g(xy)^k ≠ g(xy)^j x` by (D2). Call
`g(xy)^k` the **even** and `g(xy)^k x` the **odd** vertices of `F_g`.

**Each edge lies in exactly two 2-cells.**
- The `x`-edge `{g, gx}` lies in `F_g` (as `g -> gx`) and in `F_{gx}` (as
  `gx -> gx x = g`). These are different by (D2). It lies in no triangle.
- The boundary `y`-edges of `F_h` are `{h(xy)^k x, h(xy)^k x y}`, that is
  `{h', h'y}` with `h' = h(xy)^k x`. So `{g, gy}` lies in exactly one 14-gon,
  `F_{gx}`, and in exactly one triangle, `g<y>`.

**Link of a vertex `g`.** The 2-cells at `g` are the triangle `g<y>`, the
14-gon `F_g` (where `g` is even) and the 14-gon `F_{gx}` (where `g` is odd).
Their corners at `g` are:
- `(gY, gx)` in `F_g`, because `g(xy)^-1 x = gY`;
- `(gx, gy)` in `F_{gx}`;
- `(gy, gY)` in `g<y>`.

So the link is one 3-cycle on `{gx, gy, gY}`. Therefore `K` is a surface
without boundary. It is simply connected and noncompact, since it has infinitely
many cells by (D1) and is locally finite. By the classification of simply
connected surfaces, `K` is homeomorphic to `R^2`. Hence `G_S` is properly
embedded in the plane, its faces are exactly the triangles `g<y>` and the
14-gons `F_g`, and the cyclic order at `g` is `(Y, x, y)`, read as neighbours
`gY, gx, gy`.

## 2. G_T is planar, and its faces

The new edges are `{g, gxy}`. The pair `{g, gxy}` equals
`{h, h(xy)^-1}` for `h = gxy`, and `h<xy> = g<xy>`. So every new edge joins
two cyclically consecutive even vertices `g(xy)^k`, `g(xy)^(k+1)` of exactly
one 14-gon `F_g`. Draw it as a chord inside `F_g`. The seven chords of `F_g`
form an inscribed heptagon through its even vertices. They are pairwise
disjoint in the open face, because they join cyclically consecutive points of
the even subsequence of the boundary. This gives a proper plane embedding of
the simple graph `G_T`, with rotation `(Y, (xy)^-1, xy, x, y)` at each vertex.
The two chords at `g` sit in the corner `(gY, gx)` of `F_g`, with the chord to
`g(xy)^-1` next to `gY`.

The faces of `G_T` are:
- **Y** (size 3): the triangles `g<y>`, unchanged.
- **H** (size 7): one central heptagon per `F_g`, bounded by the seven chords.
- **C** (size 3): seven cut triangles per `F_g`,
  `C_(g,k) = (g(xy)^k, g(xy)^k x, g(xy)^(k+1))`. Each has one `x`-edge, one
  `y`-edge (`g(xy)^k x -> g(xy)^k x y = g(xy)^(k+1)`) and one chord.

**Hypotheses of the imported theorem.** `G_T` is transitive (a Cayley graph),
planar (above), nonamenable and one-ended (D3). The same holds for `G_S`.
So `fpbs-bs-planar-transitive-dual-threshold-identity` gives:
- `p_c(G_T) < p_u(G_T)` and `p_c(G_S) < p_u(G_S)`, so both sets are gapped;
- `p_u(G_T) = 1 - p_c(G_T†)`.

## 3. The dual G_T† and p_c(G_T†) >= 1/lambda

Dual adjacencies are read off across each edge of `G_T`.
- A `y`-edge lies in one triangle `g<y>` and in exactly one 14-gon (Section 1).
  Inside that 14-gon it lies in exactly one cut triangle, since each of the 7
  boundary `y`-edges is the `y`-edge of exactly one `C_(h,k)`. So it gives a
  Y--C adjacency.
- An `x`-edge lies in two 14-gons (Section 1), and in each in exactly one cut
  triangle. So it gives a C--C adjacency, with the two triangles in different
  14-gons.
- A chord lies in one cut triangle and in the heptagon of its 14-gon. So it
  gives a C--H adjacency.

Hence in `G_T†`:
- every Y-vertex has 3 neighbours, all of type C;
- every C-vertex has exactly one neighbour of each type Y, C, H, across its
  `y`-edge, `x`-edge and chord;
- every H-vertex has 7 neighbours, all of type C.

The dual is simple. Each edge of `G_T` borders two distinct faces. Distinct
edges of one face lead to distinct faces, because a C-face has only one edge of
each kind and a Y-face or H-face touches each C-face in at most its one
`y`-edge or its one chord.

**Non-backtracking count.** A self-avoiding path in `G_T†` is a
non-backtracking walk. Record the state of a walk after each step (at least
one) as the type of the current vertex together with the type of the previous
one. The states are:

| state | at | came from | next states (count) |
| --- | --- | --- | --- |
| `a` | C | Y | `b` (to C), `h` (to H) |
| `b` | C | C | `y` (to Y), `h` (to H) |
| `c` | C | H | `y` (to Y), `b` (to C) |
| `y` | Y | C | `a` twice |
| `h` | H | C | `c` six times |

With the order `(a, b, c, y, h)` this is

```text
M = [[0,1,0,0,1],[0,0,0,1,1],[0,1,0,1,0],[2,0,0,0,0],[0,0,6,0,0]],
det(zI - M) = z^5 - 8 z^2 - 12 z - 24.
```

`M` is irreducible, via `a -> b -> y -> a` and `a -> h -> c -> b`. Its Perron
root is `lambda = 2.542374251...`, the only positive root. The number of
non-backtracking walks of length `n` from any dual vertex is at most
`7 * 1^T M^(n-1) 1 <= C lambda^n`.

For Bernoulli(`q`) bond percolation on `G_T†` with `q < 1/lambda`,

```text
P(v ↔ ∞) <= P(some open self-avoiding path of length n starts at v) <= C (q lambda)^n -> 0.
```

So `p_c(G_T†) >= 1/lambda`, and by Section 2

```text
p_u(G_T) = 1 - p_c(G_T†) <= 1 - 1/lambda.
```

`check.py` confirms the combinatorics and the value of `lambda` on the
finite quotient `PSL(2,7)`. With the same rotation system, it traces the faces
of `Cay(PSL(2,7),T)`:
- 56 Y-faces, 168 C-faces and 24 H-faces;
- Euler characteristic `-4`, the Klein quartic;
- the same dual degree pattern, with a simple dual;
- non-backtracking Perron root `2.5423742510881`, equal to that of `M`.

The finite quotient has the same Perron root because `G_T†` and the finite dual
have the same universal cover.

## 4. p_c(G_S) >= p*, by a detour-weighted count

Fix `o = e` and Bernoulli(`p`) bond percolation on `G_S`. Encode a path from
`o` by its word in `{x, y, Y}`. The word determines the path, since the graph
is simple. Call a word **admissible** if it contains none of the factors `xx`,
`yY`, `Yy`, `yyy`, `YYY`. The first three would backtrack, and the last two
would return to a vertex, since `y^3 = e`. Every self-avoiding path has an
admissible word.

A **detour** of a self-avoiding path is a factor `yy` or `YY`. It visits
`g, gy^±1, gy^±2`, and the endpoints `g` and `gy^±2 = gy^∓1` are joined by the
`y`-edge `{g, gy^∓1}`, its **chord**, which is not on the path. For a
self-avoiding path `pi` let `d(pi)` be its number of detours. The chords of
distinct detours are distinct, because they join distinct pairs of path
positions `{i, i+2}`. They are also not edges of `pi`, because their endpoints
are not consecutive on `pi`.

**Reduction to a count.** Suppose the open cluster of `o` is infinite. Since
`G_S` is locally finite, for each `n` the cluster contains a vertex `v` with
`d_(G_S)(o,v) >= n`. Let `gamma` be a shortest open path from `o` to `v`, so
`|gamma| >= n`. Its length-`n` prefix `pi` is an open self-avoiding path. Every
chord of every detour of `pi` is closed: an open chord would shorten `gamma` by
one. The chords are distinct from each other and from the edges of `pi`. So

```text
theta(p) <= W_n(p) := sum over admissible words w of length n of  p^n (1-p)^(d(w)).
```

**The count.** In an admissible word, the maximal runs of letters from
`{y, Y}` are one of `y`, `Y`, `yy`, `YY`, and consecutive runs are separated by
a single `x`. So a word is `[R] (x R)^k [x]`, where the brackets are optional.
Give each letter weight `p` and each complete run `yy` or `YY` the extra factor
`(1-p)`. A final run cut short by the length-`n` truncation is simply a shorter
run in this encoding, and it carries no chord. Summing over all lengths,

```text
sum_n W_n(p) <= (1 + b)(1 + p) sum_k (p b)^k,     b = 2p + 2p^2(1-p),
p b = w(p) := 2 p^2 (1 + p - p^2).
```

`w` is increasing on `(0,1)`, since `w'(p) = 2p(2 + 3p - 4p^2) > 0`. It has
`w(0) = 0` and `w(1) = 2`. Let `p*` be its unique root of `w = 1` in `(0,1)`.
For `p < p*` the series converges, so `W_n(p) -> 0`, so `theta(p) = 0`. Hence

```text
p_c(G_S) >= p* = 0.6372776105...
```

This is not used, but `p*` is also `p_c` of the triangle cactus
`Cay(Z/2 * Z/3, {x, y, Y})`, the cover of `G_S` that forgets the relation
`(xy)^7`. There the count above is exact, and the cluster is a branching
process of mean `w(p)`. So the bound is the cover threshold, consistent with
covers having thresholds at most those of their quotients.

## 5. Conclusion, with a rational certificate

Since `z^5 - 8z^2 - 12z - 24` has derivative `5z^4 - 16z - 12 > 0` for
`z >= 2`, and its value at `z = 2.5424` is `383617429449/95367431640625 > 0`,
we get `lambda < 2.5424`. Then

```text
p_u(G_T) <= 1 - 1/lambda < 1 - 1/2.5424 = 0.60667086... < 0.6067.
```

Also `w(0.6067) = 0.91183... < 1`, so `p* > 0.6067`. Therefore

```text
p_u(Cay(Delta,T)) < 0.6067 < p* <= p_c(Cay(Delta,S)),
```

with numerical values `0.606667 < 0.637278`. Section 2 shows `T` is gapped,
and `T -> S` removes the product pair `t = xy = x·y` with `x, y ∈ S`. So
`(R*)` fails. Since `p_u(S) >= p_c(S)`, also
`p_u(S) - p_u(T) > p* - 0.6067 > 0.03`. `check.py` verifies the exact
inequalities in rational arithmetic; its output is in `output.txt`.
