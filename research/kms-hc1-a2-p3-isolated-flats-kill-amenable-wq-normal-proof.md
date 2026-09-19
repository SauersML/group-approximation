---
rg: 2
id: kms-hc1-a2-p3-isolated-flats-kill-amenable-wq-normal-proof
kind: route
title: Pappus links have exactly two geodesics between antipodal vertices, so X_3 has no flat triplane; Hruska and Hruska--Kleiner give relative hyperbolicity, and almost malnormal elementary subgroups trap every wq-normal chain
target: kms-hc1-a2-p3-isolated-flats-kill-amenable-wq-normal
requires: [kms-hc1-root-word-infinite-in-a2-quotient]
---

Notation is as in the claim. `E` is the directory
`experiments/kms-hc1-a2-p3-ozawa-sos-2026-09-19`.

## 1. The complex X_3 and its links

`Gamma_3` is the colimit of the triangle of groups `T` with vertex groups
`U_ab`, `U_bc`, `U_ca`, edge groups `<a>`, `<b>`, `<c>` of order 3, and a
trivial face group. The presentation in the claim is exactly the colimit
presentation. `U_xy = <x,y | x^3, y^3, [x,y,x], [x,y,y]>` is Heisenberg of
order 27, via `x -> E_12` and `y -> E_23` in `SL_3(F_3)`.

The link at the `U_xy` vertex is the coset graph `L`:

- its vertices are `u<x>` and `u<y>`;
- its edges are the elements `u` of `U_xy`.

`E/link_geodesics.py` builds `L` and verifies the following
(`link_geodesics.out`):

- 18 vertices and 27 edges;
- cubic, girth 6, diameter 4;
- distance-regular with levels `(d,b_d,c_d) = (0,3,0),(1,2,1),(2,2,1),(3,1,2),(4,0,3)`;
- exactly 2 geodesics between any two vertices at distance 3.

The three vertex groups are isomorphic by `a -> b -> c -> a`. That map
carries the pair of edge subgroups to the pair of edge subgroups, so all
three links are isomorphic to `L`.

Give the face the equilateral Euclidean metric. The Gersten--Stallings angle
at each vertex is then `2pi/girth = pi/3`, and the three angles sum to `pi`.
So `T` is non-positively curved. By the Gersten--Stallings theorem
(Bridson--Haefliger, Ch. II.12), `T` is developable, the local groups embed, and the
development `X_3` is a CAT(0) piecewise-Euclidean 2-complex. Its links
(Bridson--Haefliger, Ch. I.7 and II.5) are:

- `L`, with edge length `pi/3`, at vertices;
- a theta graph, at interior points of edges;
- a circle of length `2pi`, at interior points of triangles.

The theta graph has two poles, the directions along the edge, joined by 3
arcs of length `pi`. There are three arcs because the triangle stabilizers
are trivial and the edge `g<x>` lies in exactly the 3 triangles `gx^k`.
`Gamma_3` acts properly and cocompactly, and simply transitively on
triangles.

## 2. No flat triplanes

Suppose `f: Y -> X_3` is an isometric embedding of a flat triplane `Y`, and
let `l` be the image of the spine. Fix `p` in `l`. Let `Lk(p)` be the space of
directions at `p`, and let `ang = min(pi, d_Lk)` be the angle metric
(Bridson--Haefliger, Ch. I.7 and II.5).

`f` is isometric on all of `Y`, so it preserves Alexandrov angles between
geodesic segments at `p`. Let `xi+`, `xi-` be the two directions of `l`. The
directions into half-plane `i` form a half-circle `s_i`. Its parameter
`theta` in `[0,pi]` has `ang(s_i(theta), s_i(theta')) = |theta - theta'|`.
So `s_i` is a path of length `pi` in `Lk(p)` from `xi+` to `xi-`. For
`i != j` and `theta, theta'` in `(0,pi)`, we have

```text
d_Lk(s_i(theta), s_j(theta')) >= min(pi, theta + theta', 2pi - theta - theta') > 0.
```

So `s_1, s_2, s_3` are three internally disjoint paths of length `pi`. Since
`ang(xi+,xi-) = pi`, each of them is a geodesic of `Lk(p)`. In particular
`xi+` and `xi-` are branch points of `Lk(p)`, of valence at least 3.

- **`p` interior to a triangle.** A circle has no branch point. Impossible.
- **`p` interior to an edge.** The only branch points of the theta graph are
  its poles. So `l` is tangent to the edge at `p`. A geodesic of a
  piecewise-Euclidean complex leaving `p` along an edge runs along that edge
  up to its endpoint. So `l` contains a vertex of `X_3`.
- **`p` a vertex.** Here `xi+` and `xi-` are vertices of `L`. A geodesic of
  length `pi = 3 * (pi/3)` between them is an edge path of length 3 that is
  a geodesic of `L`. So `d_L(xi+,xi-) = 3`, and there would be three distinct
  geodesics between them. By section 1 there are exactly two. Impossible.

Every point of `l` falls in one of these cases. The edge case forces a
vertex onto `l`, and the vertex case is impossible. So no triplane exists.

## 3. Isolated flats and relative hyperbolicity (literature)

- Hruska (Geom. Topol. 8 (2004) 205–275) proves the following. Let `X` be a
  CAT(0) piecewise-Euclidean 2-complex with finitely many shapes and a
  proper cocompact action. Then `X` has isolated flats iff it contains no
  isometrically embedded flat triplane. With section 2, `X_3` has isolated
  flats.
- Hruska--Kleiner (Geom. Topol. 9 (2005), Thm 1.2.1) then say that
  `Gamma_3` is hyperbolic relative to its maximal virtually abelian
  subgroups of rank `>= 2`. These are the flat stabilizers, and here they
  are virtually `Z^2`.
- `Gamma_3` contains `<r,s> = C_3*C_3` (`kms-hc1-root-word-infinite-in-a2-quotient`).
  So it is not virtually abelian, and the structure is non-elementary.

## 4. The explicit Z^2

`E/tube.py` certifies that a word `w` is trivial in `Gamma_3`. It takes the
Cayley 2-complex of a finite quotient `Q`, with all relator cells. Its
universal cover maps to the simply connected Cayley complex of `Gamma_3`.
The certificate shows the loop of `w` is null-homotopic inside a finite tube,
by killing edges with a spanning tree and propagating through the cells.
This is sound for every `Q`. `E/flat_certs.py`, run on `Gamma_3/P_5` (`E/q5j3.txt`),
proves:

- `[bcba, babc] = 1` and `[bcba, baCa] = 1`;
- `(ba)^-1 bcba (ba) = AcAB`;
- `bcba^-1 = Acbc`, `babc.bcba = bcAc` and `babc.bcba^-1 = ABCabc`.

Every finite subgroup of `Gamma_3` fixes a point of `X_3`, so it lies in a
conjugate of a vertex group, of exponent 3. So `x^3 != 1` in a quotient
proves that `x` has infinite order. This holds for `u`, `v` and `baCa`
(`flat_certs.out`). It holds for `vu^-1`, of order 9 in `Gamma_3/P_7`,
by `flat_rank.out`.

Rank. Suppose `A = <u,v>` were virtually cyclic. `A` is abelian, so
`A = Z x F` with `F` finite abelian. `F` lies in a conjugate of a Heisenberg
group of order 27, so `F <= (Z/3)^2`. For every quotient `M` of `Z x F`, the
group `3M` is cyclic. But `E/flat_rank.g` finds that the image of `A` in
`Gamma_3/P_7` (order `3^22`) is `Z/9 x Z/9`. It is also `Z/9 x Z/27` in
`Gamma_3/P_8` (`flat_rank.out`). In both, `3M` is not cyclic. So `A` has
rank 2, `Gamma_3` contains `Z^2` and is not hyperbolic.

## 5. The obstruction

Let `A` be an infinite amenable subgroup. Look at the convergence action of
`Gamma_3` on its Bowditch boundary. By Tukia's classification, `A` is one of
two kinds:

- **parabolic.** Then `A` lies in a unique maximal parabolic subgroup `E`,
  a conjugate of a peripheral;
- **virtually cyclic, containing a loxodromic `h`.** Then `A <= E = E(h)`.

In both cases `E` is almost malnormal: `|gEg^-1 cap E| = infinity` implies
`g in E`. For peripherals this is Osin (Mem. AMS 843, 2006). For `E(h)` it
is Osin (IJAC 16 (2006), Cor. 1.7), because `Gamma_3` is hyperbolic relative
to the peripherals together with `E(h)`.

Take a wq-normal chain `A = H_0 <= H_1 <= ...`. At successor stages
`H_(k+1)` is generated by those `g` with `|gH_k g^-1 cap H_k| = infinity`,
and limit stages are unions. If `H_k <= E`, every such `g` has
`|gEg^-1 cap E| = infinity`, so `g` is in `E`. By transfinite induction
every stage lies in `E`. But `E` is amenable and `Gamma_3` is not, so
`E != Gamma_3`. q-normal and s-normal chains are special cases.

Now take a commuting chain `g_1 ~ g_2 ~ ...` of infinite-order elements,
with `[g_i, g_(i+1)] = 1`, and let `E = E(<g_1>)`. Suppose `g_i` is in `E`.
Then `g_(i+1) E g_(i+1)^-1 cap E` contains `g_(i+1)<g_i>g_(i+1)^-1 = <g_i>`,
which is infinite. So `g_(i+1)` is in `E`. By induction every `g_i` lies in
the proper subgroup `E`. This proves part 5 of the claim.

The data agree: `E/wqclosure.py` computes, exactly in the certified ball,
the wq-closure of `<bcba>`, and it stalls (`wqclosure.out`).

## 6. Reduction (part 6)

Suppose `Gamma_3` acts properly and cocompactly on a CAT(0) cube complex.

- With virtually abelian peripherals it is then virtually compact special
  (Groves--Manning, J. Topol. 2022; Oregón-Reyes, Geom. Topol. 2023). These
  are cited and not re-verified here.
- Schreve (Math. Ann. 359 (2014)) proves the strong Atiyah conjecture for
  such groups. The lcm of the finite subgroup orders is 27, so
  `b_1^(2)(Gamma_3)` is in `(1/27)Z`.
- Lane w26 gives `b_1^(2)(Gamma_3) <= 0.006258`, so then
  `b_1^(2)(Gamma_3) = 0`.

Niblo--Reeves: a group with (T) acting on a CAT(0) cube complex has a global
fixed point. So a cubulation would also refute (T).

## Reproduction

- `flat_certs.py` uses the shipped `E/q5j3.txt`.
- `sdp_sym.py` (`sos_runs.out`, radii 2..4) needs a ball of radius 8 that
  is certified exact. `wqclosure.py` (`python3 wqclosure.py q8pc.txt 7 bcba 6 40`)
  needs radius 14.
- The quotient tables for these are 1–40 MB and are not shipped. Regenerate
  them with `gap -q -c "K:=7;;J:=4;;" E/export_pc.g > q7j4.txt`, and with
  `K:=8;;J:=5;;` for `q8pc.txt`.
