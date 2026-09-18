---
rg: 2
id: type-a-actors-split-only-over-orbit-finite-edges-proof
kind: route
title: Attach to each point a canonical subtree, bound their pairwise distances by pair-orbit finiteness, use Helly and minimality to make each one the whole tree, then count orbits on X times edges both ways
target: type-a-actors-split-only-over-orbit-finite-edges
requires: []
---

Notation: `G` finitely generated acts on `X` with finitely generated point
stabilizers `P_x` and finitely many orbits of two-element subsets. `G` acts
without inversions on a simplicial tree `T`, minimally, with no fixed vertex and
no invariant end. `d` is the path metric on vertices. Subtrees are full
subcomplexes; `N_r(Y)` is the subtree spanned by the vertices within distance
`r` of a subtree `Y`. Trivial cases: if `X` is empty, (2) holds vacuously and
(1) is empty.

## Step 0: tree facts used

- **(F1) Elliptic groups.** A finitely generated group acting without
  inversions all of whose elements fix a vertex has a global fixed vertex
  (Serre, *Trees*, §I.6.5). Its fixed set is a subtree.
- **(F2) Axes.** A hyperbolic `h` has an axis `Ax(h)`, a line on which it
  translates by `l(h) > 0`. For every vertex `y`, the geodesic `[y, hy]` passes
  through the projection of `y` to `Ax(h)` (Serre, *Trees*, §I.6.4). Hence every
  nonempty `h`-invariant subtree `Y` contains `Ax(h)`: it contains that
  projection `p` together with all `h^n p`, and it is convex.
- **(F3) Projections.** For a subtree `Y` and a vertex `o`, the geodesic from
  `o` to any point of `Y` passes through the nearest point `proj_Y(o)`.
- **(F4) Helly.** Finitely many pairwise-intersecting subtrees have a common
  vertex. For three subtrees, pick `a in Y_1∩Y_2`, `b in Y_2∩Y_3`,
  `c in Y_1∩Y_3`; the median of `a, b, c` lies in all three. For `n`
  subtrees, replace `Y_{n-1}, Y_n` by `Y_{n-1}∩Y_n`, which meets every other
  `Y_i` by the three-subtree case, and induct.
- **(F5) No leaves.** A minimal tree without fixed vertex has no vertex of
  degree 1. The leaves form an invariant set. Deleting them leaves an invariant
  subtree, which is proper unless `T` is a vertex or an edge, and both of those
  have a fixed vertex since there are no inversions.
- **(F6) Finite groups.** A finite group acting without inversions fixes a
  vertex. Apply (F1): every element of a finite group is elliptic, because a
  hyperbolic element has infinite order.

## Step 1: canonical subtrees

Every `P_x` is finitely generated, so by (F1) either it fixes a vertex or it
contains a hyperbolic element. Put

- `S_x = Fix(P_x)` in the first case,
- `S_x` = the convex hull of the union of the axes of all hyperbolic elements of
  `P_x` in the second case.

In both cases `S_x` is a nonempty subtree. Since `P_{gx} = g P_x g^-1`, it is
equivariant: `S_{gx} = g S_x`.

## Step 2: bounded pairwise distances

`delta({x,y}) = d(S_x, S_y)` is constant on `G`-orbits of two-element subsets,
by equivariance. There are finitely many orbits, so `delta <= R` for some
integer `R`. Hence for all `x, y` the subtrees `N_R(S_x)` and `N_R(S_y)` meet,
at a vertex of the bridge between `S_x` and `S_y`.

## Step 3: a common vertex

`G` is countable and `X` has finitely many `G`-orbits: a sequence of points in
distinct orbits gives two-element subsets `{x_1, x_j}` in distinct orbits. So
`X` is countable. Enumerate it as `x_1, x_2, ...` and put
`Z_n = N_R(S_{x_1}) ∩ ... ∩ N_R(S_{x_n})`. Each `Z_n` is nonempty by (F4), and
the `Z_n` decrease. Fix a vertex `o` and put `p_n = proj_{Z_n}(o)`. Since
`p_{n+1} in Z_n`, (F3) says `[o, p_{n+1}]` passes through `p_n`.

- **Bounded case.** If `d(o, p_n)` is bounded, it is eventually constant, so
  `p_n` is eventually constant. That vertex lies in every `Z_n`, so
  `Z = ∩_x N_R(S_x)` is nonempty.
- **Unbounded case.** Otherwise the `p_n` lie on a ray `rho` from `o` whose tail
  beyond `p_n` lies in `Z_n`. Its end `xi` has property (P): for every `x`, some
  ray to `xi` lies in `N_R(S_x)`. Suppose `Z` is empty and `xi' != xi` also has
  (P). A subtree containing rays to two distinct ends contains the line between
  them, so that line lies in every `N_R(S_x)`, contradicting `Z` empty. So `xi`
  is the unique end with (P). Property (P) is `G`-invariant because
  `g N_R(S_x) = N_R(S_{gx})`, so `xi` is a `G`-invariant end, which is excluded.

So `Z` is nonempty. `Z` is a `G`-invariant subtree, so `Z = T` by minimality,
and `N_R(S_x) = T` for every `x`.

## Step 4: each canonical subtree is the whole tree

Suppose a vertex `v` is not in `S_x`, and let `p = proj_{S_x}(v)`. The component
`B` of `T - {p}` containing `v` misses `S_x`. For `w in B`, the geodesic from
`w` to `S_x` runs through `p`, so `d(w, p) = d(w, S_x) <= R`. Choose `w in B`
with `d(w, p)` maximal; this is possible because the distances are integers
between 1 and `R`. Any neighbour of `w` other than the one towards `p` would lie
in `B` farther from `p`. So `w` has degree 1, contradicting (F5). Hence
`S_x = T`.

## Step 5: point stabilizers are not elliptic

Suppose `P_x` fixes a vertex. Then `T = S_x = Fix(P_x)`, so `P_x <= N`, where
`N` is the kernel of `G -> Aut(T)`.

- **An invariant.** For a two-element subset `{ax, bx}` of the orbit `Gx`, the
  unordered pair `{a^-1 b N, b^-1 a N}` of elements of `Q = G/N` is well
  defined. Replacing `a` by `ap` and `b` by `bp'` with `p, p' in P_x <= N`
  changes `a^-1 b N` to `p^-1 a^-1 b N = a^-1 b N`, because `N` is normal and
  contains `p` and all its conjugates. The pair is unchanged under
  `(a, b) -> (ga, gb)`.
- **Infinitely many values.** Every `g notin N` moves `x`, since `P_x <= N`.
  So the invariant takes every value `{qN, q^-1 N}` with `q != 1` in `Q`.
- **Contradiction.** `Q` acts on `T` without inversions and without a fixed
  vertex, so it is infinite by (F6). Then `G` has infinitely many orbits of
  two-element subsets, which is a contradiction.

So `P_x` contains a hyperbolic element, and `S_x` is the hull of its axes, which
equals `T`. This proves the first two assertions of (1).

## Step 6: cocompactness

Let `s_1, ..., s_k` generate `P_x`, fix a vertex `o`, and put
`Y = P_x · ([o, s_1 o] ∪ ... ∪ [o, s_k o])`.

- `Y` is connected: `h[o, s_i o]` joins `ho` to `h s_i o`, and every `h in P_x`
  is a word in the `s_i^{±1}`.
- `Y` is `P_x`-invariant.
- `P_x \ Y` has finitely many edges, at most the number of edges of the finite
  union.

By (F2), `Y` contains the axis of every hyperbolic element of `P_x`, so it
contains their hull `T`. So `Y = T` and `P_x \ T` is finite. The graph-of-groups
description is the structure theorem (Serre, *Trees*, §I.5.4), with vertex
groups the stabilizers `P_x ∩ G_v`. This proves (1).

## Step 7: orbit counting

`X` is a finite union of orbits `G x_1, ..., G x_m`. Let `E` be the set of
edges of `T`. Count the `G`-orbits on `X × E` in two ways.

- **By points.** Orbits of pairs `(x, e)` with `x in G x_j` correspond to
  `P_{x_j}`-orbits on `E`, and there are finitely many by (1). So `X × E` has
  finitely many `G`-orbits.
- **By edges.** For a fixed edge `e`, the `G_e`-orbits on `X` correspond to the
  `G`-orbits on `X × Ge` via `y -> (y, e)`. These form a subset of the finitely
  many `G`-orbits on `X × E`.

So `G_e` has finitely many orbits on `X`. The same count on `X × V(T)` gives the
statement for `G_v`. This proves (2).

## Step 8: irreducible Bass--Serre trees

**Amalgams.** Let `G = A *_C B` with `C != A, B`, and let `T` have vertex set
`G/A ⊔ G/B` and edge set `G/C`.

- **No leaves.** A vertex `gA` has degree `[A : C] >= 2`, and likewise for
  vertices `gB`.
- **Minimal.** An invariant subtree contains some vertex, hence every vertex of
  that type (one orbit per type), hence every geodesic between two such
  vertices. Each vertex of the other type has at least two neighbours, both of
  the first type, so it lies on such a geodesic. So the subtree contains all
  vertices and is `T`.
- **No fixed vertex.** A fixed vertex would force `G = gAg^-1` or `G = gBg^-1`,
  so `B <= A` or `A <= B`, which is impossible when `C != A, B`.
- **No invariant end.** Suppose `xi` is invariant. The vertex stabilizer
  `A = G_{v_A}` fixes `v_A` and `xi`, so it fixes the ray from `v_A` to `xi`,
  and in particular its first edge. Edge stabilizers at `v_A` are `aCa^-1` with
  `a in A`. So `A <= aCa^-1`, which forces `A = C`, a contradiction.

**HNN extensions.** Let `G = A *_phi` with `phi : C_1 -> C_2` and `C_1, C_2 != A`.

- **No leaves.** Each vertex has degree `[A : C_1] + [A : C_2] >= 2`.
- **Minimal.** There is one vertex orbit, so an invariant subtree contains every
  vertex and is `T`.
- **No fixed vertex.** `t` is hyperbolic.
- **No invariant end.** The edge stabilizers at the base vertex are conjugates
  in `A` of `C_1` and `C_2`, so the argument above gives `A = C_1` or `A = C_2`,
  a contradiction.
