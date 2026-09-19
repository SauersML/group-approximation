---
rg: 2
id: fpbs-cle6-hull-wedge-event-is-not-the-box-event-proof
kind: route
title: Proof that the CLE_6 hull wedge event is a strict, much rarer sub-event of the circuit box event (duality, half-plane one-arm bound, pinch lemma, triangular-lattice numerics)
target: fpbs-cle6-hull-wedge-event-is-not-the-box-event
requires:
  - fpbs-geodesic-bisector-chain-polynomial-in-inverse-theta
---

Notation is as in the claim. We work with site percolation on the
triangular lattice at `p = 1/2`, each site a hexagon of the dual
honeycomb, in axial coordinates `(i,j)` with position
`x = i + j/2`, `y = j sqrt(3)/2`. The neighbours of `(i,j)` are
`(i,j) + d_k` for the cyclic list
`d = (1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1)`. Consecutive `d_k`,
`d_{k+1}` are neighbours of each other, so `c + d_{k±1}` are the two
*common neighbours* of `c` and `c + d_k`.

`B_n = {|j| <= n, |2i+j| <= 2n}` is the rectangle `|x| <= n`,
`|y| <= n sqrt(3)/2`. Sites of `B_n` with a neighbour outside `B_n` are
the boundary `∂B_n` and are declared black. `I_n` is the black cluster of
`∂B_n` in `B_n`. A *hole* is a connected component of `B_n \ I_n`.
`S_n = {(i,0): -n < i <= 0}`, `X = {x > 0}`, `R = {(i,0): 1 <= i < n}`
(so `R ⊆ X`).

**Two facts used throughout.**

(F1) A white site is never in `I_n`, so every connected set of white
sites lies in a single hole.

(F2) *(Jordan property.)* If `C` is a white circuit in `B_n`, i.e. a
cyclic sequence of distinct neighbouring white sites whose polygon
through the site centres is a Jordan curve, then no site of `I_n` lies in
the bounded component of the complement of that curve. The reason: such
a site has a black path to `∂B_n`. The sites of `∂B_n` are all outside
the curve, since the curve lies in `B_n` and every boundary site is
extreme. Every lattice edge crossing the curve has an endpoint on `C`.

## (a) `H_n ⊆ D_n`

Suppose `D_n` fails. Take a white circuit `C` that surrounds
`v = (a,0) ∈ S_n` and contains a site `w ∈ X`. The row-0 sites
`(i,0)`, `-n <= i <= a`, form a lattice path from `(-n,0) ∈ ∂B_n` to `v`.
The curve of `C` separates `v` from `∂B_n`, so that path meets `C`. On the
triangular lattice, edges meet only at sites, and the row-0 segment
consists of sites and edges of the lattice.

Let `u = (i,0)` be a site where the path meets `C`. Then `u ≠ (-n,0)`,
because boundary sites are black and `C` is white. So
`-n < i <= a <= 0` and `u ∈ S_n`. By (F1), `C` lies in one hole, and
that hole contains `u ∈ S_n` and `w ∈ X`. So `H_n` fails. ∎

So `P(D_n) >= P(H_n)`. The hull event is a sub-event of the box event.
It could therefore prove (H) only if its own exponent were `< 3/8`.

## (b) `H_n` forces black half-plane arms

Let `Q = B_n ∩ {j >= 0}` and let `D` be the union of the closed hexagons
of the sites of `Q`. `D` is a closed topological disc. Split its boundary
Jordan curve `∂D` into four consecutive arcs:

* `α`: the lower edges of the hexagons `(i,0)`, `-n < i <= -1`;
* `δ`: the lower edges of the hexagons `(0,0)` and `(1,0)`;
* `β`: the lower edges of the hexagons `(i,0)`, `2 <= i < n`;
* `γ`: the rest of `∂D`.

The lower edges of a hexagon `(i,0)` are those shared with `(i,-1)` and
`(i+1,-1)`. So consecutive row-0 hexagons have lower edges that meet at a
vertex, and `α, δ, β` are consecutive arcs.

*Four-arc duality (Hex lemma).* For any colouring of the hexagons of a
closed disc `D` that is a union of hexagons, with `∂D` split into four
arcs `α, δ, β, γ` in cyclic order, exactly one of the following holds:

* a white path of hexagons of `D` joins a hexagon with an edge on `α` to
  one with an edge on `β`;
* a black path of hexagons of `D` joins a hexagon with an edge on `δ` to
  one with an edge on `γ`.

This is the standard exploration-path argument; see Werner, *Lectures on
two-dimensional critical percolation*, §1.

On `H_n` the first alternative is impossible. Such a white path is
connected, so by (F1) it lies in one hole. That hole contains a hexagon
with an edge on `α`, which is a site of `S_n`, and a hexagon with an edge
on `β`, which is a site of `R ⊆ X`. That contradicts `H_n`.

So on `H_n` there is a black path `π` in `Q` from `(0,0)` or `(1,0)` to
a hexagon with an edge on `γ`. Every such hexagon is either a site of
`∂B_n` (at distance `>= n sqrt(3)/2 - 1` from the origin) or one of
`(±n,0)` (at distance `>= n - 1`). Truncate `π` at its first site at
Euclidean distance `>= n/2` from the origin. The truncated path is a black
path of **interior** sites of `B_n`, whose colours are i.i.d. fair. It
lies in the half-plane `{j >= 0}` and runs from a site on the line
`j = 0` to distance `n/2 - 1`.

Let `pi^+(r)` be the probability of a black path in `{j >= 0}` from the
origin to distance `r`. By translation invariance,

    P(H_n) <= 2 pi^+(n/2 - 1) = n^{-1/3 + o(1)},

using the half-plane one-arm exponent `1/3` on the triangular lattice
(Smirnov-Werner 2001; Lawler-Schramm-Werner). The mirror argument in
`B_n ∩ {j <= 0}` gives the same bound with a black arm in the lower
half-plane. So on `H_n` two such arms exist at once. They need not be
disjoint, since both may start at `(0,0)` or `(1,0)`. We do not claim a
rigorous exponent for the pair. ∎

## (c) Filled clusters, pinches, and the proxy

*Filled-cluster form.* Suppose `D_n` fails through a white circuit `C`
that surrounds `v ∈ S_n` and contains `w ∈ X`. Let `K` be the white
cluster of `C`. Its filled set `fill(K)` is `K` together with the
bounded components of the complement of `K`. The outer boundary of
`fill(K)` is again a white circuit `C'`. It lies in `K`, so in `B_n`, and
it surrounds `C`, hence `v`. The rightmost site of `K` lies on `C'`, and
its abscissa is at least `x(w) > 0`. The converse is trivial. So `D_n`
fails iff some white cluster has an outer circuit around a point of
`S_n` that meets `X`. In the scaling limit these outer circuits are
external perimeters, SLE_{8/3}-type curves of dimension 4/3, and not the
hull loops (CLE_6, dimension 7/4) that bound the holes of `I_n`.

*Pinch lemma.* A step `c -> c + d_k` is a *pinch* if both common
neighbours `c + d_{k±1}` lie in `I_n` or outside `B_n`. No white circuit
uses a pinch step.

*Proof.* Suppose a white circuit `C` uses the step. The edge
`c, c + d_k` bounds two lattice triangles, with third vertices
`e = c + d_{k-1}` and `f = c + d_{k+1}`, and near the edge's midpoint
the two triangles lie on opposite sides of the curve of `C`. The curve is
made of lattice edges, so it does not meet an open lattice triangle.
Neither `e` nor `f` lies on `C`: sites of `I_n` are black, and outside
sites are not in `B_n`. So each of `e` and `f` is on the same side as its
own open triangle, and `e`, `f` lie on opposite sides of the curve. One of them, say
`e`, is then inside the curve. `e` is not outside `B_n`, because the
curve lies in the convex region `B_n`. So `e ∈ I_n`, which contradicts
(F2). ∎

*Proxy.* Let `D'_n` be the event that no path of non-`I_n` sites, with no
pinch step, joins a site of `X` to a site of `S_n`. Then `D'_n ⊆ D_n`.
If `D_n` fails, the circuit `C` from (a) is such a path, by (F1) and the
pinch lemma, from `w ∈ X` through `u ∈ S_n`. So `D'_n` fails.

`tri_d.c` computes `D'_n` exactly, by a BFS from `X` over non-`I_n`
sites that skips pinch steps. With pinch skipping switched off it
computes `H_n` exactly, since holes are then flooded without restriction.
So `H_n ⊆ D'_n ⊆ D_n` and the numerics give

    P(H_n) <= P(D'_n) <= P(D_n).

Both inequalities are proved, but equality in the second is not. So
`exponent(D_n) <= exponent(D'_n)`, and a rigorous proof that
`P(D'_n) >= n^{-zeta'}` with `zeta' < 3/8` would prove (H) on the
triangular lattice. `D'_n`, unlike `H_n`, is a viable sub-event.

## (d) Numerics

Code is in `experiments/fpbs-cle6-wedge-exponent-2026-09-18/`
(`tri_d.c`, `pool.py`, `run_all.sh`); the output is `results.txt`. Each
sample draws one configuration on `B_N` and evaluates the events for the
nested boxes `n = 8, 16, ..., N`. Local slopes are
`-log2 P(E_n | E_{n/2})`, with 20-block jackknife errors. No
monotonicity violations occur (`E_n` without `E_{n/2}`). This was
observed, not proved.

| event | N | samples | P(E_8) | P(E_N) | local slopes (n = 16..N) |
|---|---|---|---|---|---|
| `D'_n` (pinch on) | 512 | 3000 | 0.494 | 0.154 | 0.296, 0.279, 0.306, 0.267, 0.267, 0.270 (s.e. 0.014-0.029) |
| `0 ∈ I_n` | 512 | 3000 | 0.459 | 0.286 | 0.09-0.13 (one-arm `5/48 ≈ 0.104`) |
| `H_n` (pinch off) | 256 | 3000 | 0.131 | 0.0007 | 1.10, 1.41, 1.35, 2.2, 1.6 (s.e. 0.09-1.2) |

**Reading.**

* The circuit-form proxy decays with local exponent `≈ 0.27`. That is
  stable over six doublings, far below `3/8` (about 6 s.e. at `n = 512`),
  and compatible with the Z^2 box-event value `0.251(6)`. So the
  triangular analogue of (H) is numerically true with a margin.
* The hull form decays with local exponent `>= 1`. It is a strict and
  much rarer sub-event, as (a)-(b) predict.
* The one-arm check reproduces `5/48`. This confirms that the wired
  cluster and the nested-box bookkeeping are correct.

## Conclusion

* The §3.4 CLE_6 hull route cannot prove (H) as stated. Its event `H_n`
  is a sub-event of `D_n` with rigorous exponent `>= 1/3` and measured
  exponent `>= 1`, above the gate `3/8`. The rigorous `1/3` alone would
  not exclude the route, so the obstruction rests on the numerics.
* The object that carries `zeta` is the filled-cluster / external-
  perimeter event (c). Its lattice proxy `D'_n` is a proved sub-event of
  `D_n` with measured exponent `≈ 0.27 < 3/8`.
* (H) is OPEN. The next step is a rigorous lower bound
  `P(D'_n) >= n^{-zeta'}` with `zeta' < 3/8`. Any such proof must use
  configurations where holes do connect `S_n` to `X`, but only through
  pinches. By (b), a black crosscut above the origin already costs
  `n^{-1/3}`, which leaves only a margin of `1/24` against `3/8`. The
  full hull event, with crosscuts above and below the origin, is
  numerically far too rare.
