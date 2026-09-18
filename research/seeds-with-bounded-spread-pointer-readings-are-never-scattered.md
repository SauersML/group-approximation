---
rg: 2
id: seeds-with-bounded-spread-pointer-readings-are-never-scattered
kind: claim
title: Over F × H with F free, a seed whose tree pointers can be read honestly near one common height on every tree-ball has a boundary of cardinality continuum; so a scattered seed must scatter its pointer readings across unboundedly many heights, and every known design either reads with bounded spread or violates the separation lemma
requires:
  - seeds-record-every-bass-serre-pointer
  - seed-compactifications-dominate-the-end-compactification
distinct_from:
  seeds-record-every-bass-serre-pointer: that proves the pointer exists on every column and that reading it in one bounded window gives an uncountable boundary; this allows the reading heights to vary without bound from edge to edge, and needs only that each tree-ball is read near a common height.
  seed-compactifications-dominate-the-end-compactification: that is the finite-cut case; here every cut is an infinite column F-edge × H.
---

**ESTABLISHED** (lane bh-star-a, 2026-09-18; elementary lane proof below; not reviewed; no priority
claimed). This is a partial answer to conjecture (HP) of `seeds-record-every-bass-serre-pointer` on the
test group `F_2 × Z`. It does not settle (HP).

## Setting

- `Γ = F × H`, with `F` free of rank at least 2 on a basis `S`, Cayley tree `T`, and `H` finitely
  generated with word metric `d_H`.
- `(Y, y_*)` is a seed: an SFT with windows `B_r`, satisfying (S1) and (S2).
- **Edges and columns.** Tree edges are `ε = g e_s` with `e_s = {1, s}` and frame `g`. The column of `ε`
  is `N_r(ε) × H`.
- **Deep translates.** A translate `x = (f, t).y_*` is *`D`-deep* for `ε` if `d_T(f, ε) ≥ D`. Its *side*
  at `ε` is the component of `T ∖ ε` containing `f`.
  - By `seeds-record-every-bass-serre-pointer` (products, with cut columns), the full column pattern
    determines the side.

**Honest reading scheme.** This is a width `w`, a depth `D`, and maps
`Ψ_s : A^(N_r(e_s) × B^H_w) → {near, far, ?}`.
- **Use.** Apply `Ψ_s` to the framed pattern `((g, u)^(-1).x)|_(N_r(e_s) × B^H_w)` of `x` at `(ε, u)`, for
  `ε = g e_s`.
- **Honesty.** For every `D`-deep translate `x`, every edge `ε`, and every height `u ∈ H`, a non-`?`
  output is the true side of `x` at `ε`.
- `ε` is *read at `u`* in `x` if the output is not `?`.

**Bounded spread (BS).** There are an honest scheme and a function `M : N -> N` with the following
property. For every edge `ε` and every translate `x` that is `D_x`-deep for `ε`, there is **one** height
`u = u(x, ε)` such that, for every `R ≤ D_x − D`, every edge of the tree-ball `B_R(ε)` is read in `x` at
some height within `M(R)` of `u`.

## Theorem

1. If `(Y, y_*)` has bounded spread, then `∂Y` has the cardinality of the continuum. In particular it is
   not scattered.
2. So a scattered seed over `F × H` violates (BS) for **every** honest reading scheme. For every scheme
   and every `M`, some radius `R` and arbitrarily deep translates have tree-balls `B_R(ε)` whose edges
   cannot all be read within `M(R)` of any single height.

## Proof of 1

For each infinite reduced word `ω = w_1 w_2 …` in `S^(±1)`, we build `z_ω ∈ ∂Y`. Then we show
`z_ω ≠ z_(ω')` for `ω ≠ ω'`.

- **Sequence.**
  - Put `f_n = (w_1 ⋯ w_n)^(-1)` and `ε_n = {f_n, f_n w_1}`. The geodesic from `f_n` to `1` reads
    `w_1, …, w_n`.
  - Let `u_n = u(y_*, ε_n)` be the centre given by (BS). Put
    `x_n = (f_n, u_n)^(-1).y_*`.
  - In `x_n` the seed sits at tree coordinate `w_1 ⋯ w_n`. So on `B_(n−D)(1)` the true sides are those of
    the pointer field toward the end `ω`.
- **Readings in a fixed frame.**
  - Fix an edge `ε'` of `T` and put `R = d_T(ε', e_(w_1)) + 1`. Once `n ≥ R + D`, (BS) at the centre `u_n`
    gives a reading of `f_n ε'` in `y_*` within `M(R)` of `u_n`. The bound does not depend on `n`.
  - Translating by `(f_n, u_n)^(-1)`, the edge `ε'` is read in `x_n` at a height `v_n(ε')` with
    `|v_n(ε')| ≤ M(R)`.
  - The balls of `H` are finite, so a diagonal subsequence makes every `v_n(ε')` eventually constant,
    say equal to `v(ε')`, and makes `x_n → z_ω`.
  - Then `z_ω` agrees with `x_n`, for large `n`, on the reading window of `ε'` at `v(ε')`. There the
    output is the `ω`-side of `ε'`.
  - The seeds of the `x_n` escape to infinity, so `z_ω ∈ ∂Y`.
- **Injectivity.**
  - Let `ω ≠ ω'`. Some edge `ε'` has different `ω`- and `ω'`-sides.
  - Suppose `z_ω = z_(ω') =: z`. Then `z` has a window at `(ε', v(ε'))` with output the `ω`-side, and a
    window at `(ε', v'(ε'))` with output the `ω'`-side.
  - A single deep translate `x_n` agrees with `z` on both windows for large `n`. Honesty then forces two
    different true sides for `x_n` at `ε'`, which is a contradiction.
- **Cardinality.** Infinite reduced words form a set of the cardinality of the continuum. ∎

## Which designs satisfy (BS)

In each case take `u` as indicated. Every one therefore has boundary of cardinality continuum.
- **Product and glued seeds.** `u` is the seed height, and `M ≡ 0`.
- **Light cones** (arrival time equal to tree depth). `u` is the depth of `ε`, and `M(R) = R`.
- **Homomorphism heights** `u(ε) = φ(ε)`, for `φ : F → Z`. Here `M(R) = R`.
- **Persistent schedules** (BFS, iterative-deepening DFS, or multiplicative codes in which an edge stays
  readable after its first visit). `u` is a time after the whole ball `B_(D_x − D)(ε)` has been visited,
  and `M ≡ 0`.
- **Token designs** violate (BS): information is present only where a moving token is. But they are not
  seeds. The two tokens of `y_*` and of `(f, 0).y_*` stay at tree distance at least the cyclically reduced
  length of `f`, so their difference set cannot join the two seeds. That violates the separation lemma of
  `seed-compactifications-dominate-the-end-compactification`, and a second origin can be glued in.

So no design known to this lane both is a seed and escapes (BS).

## What remains of (HP) on F × H

A scattered seed would need the following, all at once.
- **Separation.** The difference set of `y_*` and `(f, t).y_*` must coarsely join the two seeds.
  Information about the origin must therefore stay connected through the columns over the geodesic.
- **Steep reading.** Readings must spread across unboundedly many heights on tree-balls (part 2), so the
  information cannot persist on any height band covering a ball.
- **Local consistency.** The SFT must still reject every configuration with two origins, using rules of
  radius `r`.

The open question is whether a connected, locally checkable pointer structure can keep every tree-ball's
readings unboundedly spread.
- Persistence gives (BS). Pure transience breaks separation.
- A proof of (HP) on `F × H` would show that local consistency forces some persistence.

## Lesson for general BH

**A seed's knowledge of the origin cannot be both local and scattered.**
- On `F × H`, the pointer must be recorded on every column. If it can be read near a common height across
  each tree-ball, the seed's boundary is as large as `∂F`. This holds whether the reading is instant, delayed
  like a light cone, tilted by a homomorphism, or persistent like a search schedule.
- Transient designs that read with unbounded spread lose the connectivity that makes the origin unique.
- So scattered seeds, the rigidity-free route to ¬CAP, look confined to groups without free splittings.
  The case of (HP) left open is whether local consistency forces persistence.
