---
rg: 2
id: a2-seed-boundary-pointer-proof
kind: route
title: Limits toward a regular point give chamber fields; toward a vertex, agreement with one genuine field on each edge-plus-vertex apartment shows vertex labels fill fibres, pointers transport along rays, and every panel-tree edge is pointed along exactly once
target: a2-seed-boundary-is-chambers-and-panel-tree-pointers
requires:
  - a2-lattices-carry-finite-type-seeds
---

Notation and the facts (B1)–(B5) are those of the target. Write `v = v_ξ` and `π = π_ξ`.
- In an apartment, `e, f` denote unit singular vectors at `60°`. A chamber at `x` is
  `{x, x + e, x + f}`.
- Two vertices of an apartment `A` are adjacent in `Δ` iff they are adjacent in `A`, by convexity.
  Link angles between simplices of `Lk_A(x)` are intrinsic.
- Labels can be read in any apartment `A` containing `x` and `o`: `[x, o] ⊆ A`, so `a_o(x)` is the
  simplex of the hexagon `Lk_A(x)` containing the direction of `o − x`.

## Step 0. Items 1 and 2

- **The transport is the ray step.** Let `{x, x', w}` be a chamber with `x' = v(x)`. By (B2) take an
  apartment `A_ξ ⊇ {x, x', w}` with `ξ ∈ ∂A_ξ`. There `x' = x + e`, with `e` the `ξ`-direction, and
  `w = x + f`. So `v(w) = w + e = x' + f`, which is adjacent to `x'`, to `w` and to `v(x') = x' + e`.
  In the projective plane `Lk(x')`:
  - `x` and `v(x')` are opposite;
  - `w` is adjacent to `x`, so `d(w, v(x')) = 2`, and `v(w)` is their unique common neighbour;
  - conversely, for `u` adjacent to `v(x')`, `d(x, u) = 2`, and the unique common neighbour of `x` and
    `u` inverts the map.

  This is item 1. It also shows `π(v(w)) = π(w)`.
- **Item 2.**
  - *Adjacency.* In `A_ξ`, `x` and `w` lie on adjacent `ξ`-lines, so `π(w)` is adjacent to `π(x)`
    (B5).
  - *Injectivity.* If `π(w_1) = π(w_2)`, the rays from `w_1` and `w_2` eventually meet. Their `k`-th
    vertices are the iterated transports, and the transports are injective. So `w_1 = w_2`.
  - *Surjectivity.* By (B5) an edge at `π(x)` lies on the line of some `A_ξ`. Realize it there by a
    chamber at some `x̃ ∈ A_ξ` over `π(x)`. Transport it forward to the vertex where the rays of `x̃`
    and `x` meet, then backward to `x` with the inverse of item 1. The class of the other vertex is
    kept.
  - *Sectors.* For `c ∋ ξ` and `A ⊇ Q(x, c)` (B1), the germ of `Q(x, c)` is `{x + e, x + f}`, with `f`
    the other wall direction of `c`. `π(x + f)` is the neighbour of `π(x)` toward the end of `c`, by
    (B5).

## Step 1. Reduction to limits (the part already on `a2-phase-seed-passes-the-separability-test`)

- **Sequences.** By (S3) of `a2-lattices-carry-finite-type-seeds`, `y = lim y_(o_n)`. If `o_n` is
  bounded, `y = y_o`. Otherwise, by (B3), pass to a subsequence with `o_n → η ∈ ∂Δ`.
- **Directions.** By (B4), for large `n`, the direction of `[x, o_n]` lies within `60°` of that of
  `[x, η)`, so `y(x)` contains the simplex carrying that direction.
- **Regular limit.** If `η` lies in an open chamber `c`, then `y(x)` is the germ of `Q(x, c)`, and
  `y = y_c`.
- **Vertex limit.** If `η = ξ` is a vertex, then `v(x) ∈ y(x)` for every `x`: `y(x)` is the vertex
  `v(x)` or a chamber containing it.
- **Two facts used below.**
  - (F) For every finite set `F`, `y` agrees with `y_(o_n)` on `F` for all large `n`.
  - (A) An edge (or chamber) and a vertex `o` lie in a common apartment (B2).

From now on `η = ξ`. Put `S = {π(x) : y(x) = v(x)}`, and for `x` with `π(x) ∉ S` write
`y(x) = {v(x), w(x)}` and `P(x) = {π(x), π(w(x))}`.

## Step 2. Vertex labels fill fibres

Let `x' = v(x)`. Take `o = o_n` with `y = y_o` on `{x, x'}` (F), and an apartment `A ⊇ {x, x', o}` (A).
In `A` write `x' = x + e`.
- **Forward.** If `y(x) = v(x) = x'`, then `o = x + m e` with `m >= 1`.
  - `m = 1` would put `*` at `x'`.
  - So `m >= 2`, and `a_o(x') = x' + e` is a vertex. By Step 1 it equals `v(x')`.
- **Backward.** If `y(x') = v(x')`, then `[x', o]` starts along the edge `x' v(x')`. That edge is at
  `180°` from `x` in `Lk(x')`, so in `A` it is `x' + e` and `o = x' + m e`. So `a_o(x) = x'`, a vertex,
  which is `v(x)`.

Rays generate each fibre of `π` under forward and backward steps. So `{x : y(x) = v(x)} = π^(-1)(S)`.

## Step 3. Pointers transport along rays

Let `π(x) ∉ S`, `x' = v(x)` (so `π(x') ∉ S` by Step 2), and `w = w(x)`.
- **Set-up.** Take `o` with `y = y_o` on `{x, x', w}`, and `A ⊇ {x, x', w, o}` (A). In `A`,
  `w = x + f` and `o = x + a e + b f` with `a, b >= 1`.
- **`a >= 2`.** `a = 1` would make `a_o(x')` the vertex `x' + f`, but `y(x')` is a chamber. So
  `y(x') = {x' + e, x' + f}`.
- **Identifying `v(x')`.** Of these two vertices, only `x' + e` is opposite `x`, so it is `v(x')`.
- **Identifying `v(w)`.** `y(w) = a_o(w) ⊆ {w + e, w + f}` contains `v(w)`. `v(w)` is adjacent to `x'`
  (Step 0). `w + f` is not, being at distance `√3` in `A`. So `v(w) = w + e = x' + f`.
- **Conclusion.** `y(x') = {v(x'), v(w)}` is the transport of `y(x)`, and `P(x') = P(x)` by Step 0. So
  `P` descends to a function on `T_ξ \ S`, and each vertex has at most one out-edge.

## Step 4. Every edge of `T_ξ` is pointed along by exactly one endpoint

Let `{t, s}` be an edge. By item 2 choose `x` over `t` and a chamber `{x, x', w}` with `x' = v(x)` and
`π(w) = s`. By Step 0, `{w, v(w), x'}` is the chamber at `w` that item 2 sends to `{s, t}`. So:
- `t` points to `s` iff `y(x) = {x', w}`;
- `s` points to `t` iff `y(w) = {v(w), x'}`.

Take `o` with `y = y_o` on `{x, x', w}` and `A ⊇ {x, x', w, o}`, with `x' = x + e` and `w = x + f` in
`A`. `y(x) ∋ x + e`, so `o − x` lies on the ray `e` or in one of the two open cones at `e`.
- **(i) `o = x + a e`.** Then `t ∈ S`, and `a >= 2` by Step 2.
  - Then `o − w = (a − 1) e + (e − f)`, so `y(w) = {w + e, x'}`.
  - `v(w) ≠ x'` (Step 0), so `v(w) = w + e`, and `s` points to `t`.
- **(ii) `o = x + a e + b f`, with `a, b >= 1`.** Then `t` points to `s`.
  - If `b = 1`, then `y(w) = w + e` is a vertex, so `s ∈ S`.
  - If `b >= 2`, then `y(w) = {w + e, w + f}`, and `v(w) = w + e` by adjacency to `x'`. Since
    `w + f ≠ x'`, `s` does not point to `t`.
- **(iii) `o = x + a e + b(e − f)`, with `a, b >= 1`.** Then `y(x) = {x + e, x + e − f} ≠ {x', w}`, so
  `t` does not point to `s`.
  - `o − w = (a − 1) e + (b + 1)(e − f)`.
  - If `a = 1`, `y(w)` would be the vertex `x' ≠ v(w)`, which is impossible.
  - So `a >= 2`, and `y(w) = {w + e, x'}` with `v(w) = w + e`. So `s` points to `t`.

## Step 5. Conclusion

- **The orientation of `T_ξ`.** By Steps 3–4 every edge is oriented by exactly one endpoint, every
  vertex has out-degree at most 1, and the sinks are exactly `S`.
- **At most one sink.** A path between two sinks would need an edge oriented by neither end.
- **Pointer structure.** From any vertex, following out-edges never backtracks. So all edges point
  toward the unique sink `p` if `S = {p}`, or toward one end `ε` if `S = ∅`.
- **The field.** In the first case, Steps 2–3 and item 2 give `y = y_(ξ,p)`. In the second, `y(x)` is
  the chamber sent to the first edge toward `ε`, which is the germ of `Q(x, c_ε)` by item 2. So
  `y = y_(c_ε)`.
- **The three kinds are distinct.**
  - `y_o` is the only field with a `*`.
  - Chamber fields have no vertex labels.
  - `y_(ξ,p)` has vertex labels on `π^(-1)(p)` only.
  - `(ξ, p)` is read off: `ξ` is the common point at infinity of the rays formed by vertex labels,
    and `p` is their class. `∎`

**Remark.**
- **Only local tools.** The proof never uses a global apartment containing `o` together with the
  ray to `ξ`. Such an apartment need not exist, since `o` may sit on a branch that merges late into
  the relevant ray. Every step instead uses one apartment through a single edge or chamber and `o`,
  together with (F).
- **The rank-2 input.** It is Step 0: uniqueness of common neighbours in projective planes.
