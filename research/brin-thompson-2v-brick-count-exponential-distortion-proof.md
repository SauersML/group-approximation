---
rg: 2
id: brin-thompson-2v-brick-count-exponential-distortion-proof
kind: route
title: "One conjugation by the global baker map halves the level: beta B_d beta^{-1} = tau B_{d-1}, so 2^d disjoint baker pieces cost 3d+1 letters, while a brick map must read d+1 letters of the first coordinate"
target: brin-thompson-2v-brick-count-is-exponentially-distorted
requires: []
artifacts:
  - experiments/brin-thompson-cnd-2026-09-18/brick_compression.py
---

Notation is as in the target. A **brick map** `(u_1 s_1, ..., u_n s_n) |-> (U_1 s_1, ..., U_n s_n)`
sends the suffix `s_i` of coordinate `i` to coordinate `i` only; this is the defining property of
`nV` used throughout. `mu` is the product Bernoulli measure, so `[u_1] x ... x [u_n]` has measure
`2^{-sum |u_i|}`.

**Step 1 (item 1).** `supp(b_w) subset [w] x C`, and for `|w| = |w'|`, `w != w'`, the bricks
`[w] x C` and `[w'] x C` are disjoint. Disjointly supported homeomorphisms commute. If `v in V` is
the prefix-replacement permutation of level-`|w|` cylinders that swaps `[w]` and `[w']` and fixes
the others, then `(v x id) b_w (v x id)^{-1} = b_{w'}`, so the pieces are pairwise conjugate in
`V x id`.

Every point of `C^n` has a length-`d` prefix in its first coordinate, so the product of the `b_w`
over `|w| = d` acts on `[w a] x C x ... x C` by `b_w`, that is,
`B_d(w a s, t, z) = (w s, a t, z)` for `|w| = d`. In particular `B_0 = b_empty = beta`.

**Step 2 (item 2: the recursion).** Both sides are elements of `2V`, so it is enough to evaluate.
Recall `beta(a s, t) = (s, a t)`, hence `beta^{-1}(x, a t) = (a x, t)`.

Fix `d >= 1` and a point `(x, y)`. Write `y = a t` and `x = w' a' s` with `|w'| = d - 1`.

- `beta^{-1}(x, a t) = (a x, t) = (a w' a' s, t)`, and `|a w'| = d`.
- `B_d(a w' a' s, t) = (a w' s, a' t)` by Step 1.
- `beta(a w' s, a' t) = (w' s, a a' t)`.

So `(beta B_d beta^{-1})(x, y) = (w' s, a a' t)`. On the other hand
`B_{d-1}(w' a' s, a t) = (w' s, a' a t)` by Step 1, and `tau = id x rho` replaces the prefix `a' a`
of the second coordinate by `a a'`. Hence `(tau B_{d-1})(x, y) = (w' s, a a' t)` as well, and
`beta B_d beta^{-1} = tau B_{d-1}`.

Rearranged, `B_d = beta^{-1} tau B_{d-1} beta`. Iterating `d` times and using `B_0 = beta`,

  `B_d = (beta^{-1} tau)^d B_0 beta^d = (beta^{-1} tau)^d beta^{d+1}`,

a word of length `2d + (d+1) = 3d + 1` in `{beta, tau}` (`tau` is an involution). Hence
`|B_d| <= 3d + 1`. The script verifies the recursion and the closed form as identities of elements
of `2V` for `0 <= d <= 8`.

**Step 3 (item 3: the exact brick count).**

*Upper bound.* The `2^{d+1}` bricks `[w a] x C x ... x C`, `|w| = d`, `a in {0,1}`, partition `C^n`,
and on each one `B_d` is the single brick map to `[w] x [a] x C x ... x C`. The `2^{d+1}` range
bricks partition `C^n` as well. So `L(B_d) <= 2^{d+1}`.

*Lower bound.* Let `[u_1] x ... x [u_n]` be a brick of any diagram of `B_d`, and let `x` be a point
of it. The second output coordinate of `B_d` at `x` begins with letter `d+1` of the **first** input
coordinate. If `|u_1| < d + 1` then letter `d+1` of the first coordinate varies over the brick while
the first `|u_1|` letters are fixed, so the first letter of the second output coordinate varies too.
A brick map's second output coordinate is `U_2 s_2`, which depends only on the second input
coordinate. Contradiction. Hence `|u_1| >= d + 1` for every brick of every diagram, so every brick
has measure at most `2^{-(d+1)}`, and a partition of `C^n` needs at least `2^{d+1}` of them.

So `L(B_d) = 2^{d+1}` exactly. (The script recomputes this independently with the exact guillotine
DP `lib2v.min_bricks`, for `0 <= d <= 8`.) Combining with Step 2,
`log_2 L(B_d) = d + 1 >= (|B_d| - 1)/3`.

**Step 4 (item 4).** On the brick `[w a] x C x ... x C` the element `B_d` replaces the prefix `w a`
(length `d+1`) of the first coordinate by `w` (length `d`) and the empty prefix of the second by
`a`. So `c(B_d)(x) = (-1, +1, 0, ..., 0)` for every `x`: the cocycle is constant, `||c(B_d)|| = 1`
and `pd(B_d) = 0`.

**Step 5 (item 5).** `T_0 = sigma x id` flips the first letter of the first coordinate. The same
computation as Step 2, with the flip in place of the baker piece, gives
`beta T_d beta^{-1} = T_{d-1}`: indeed `beta^{-1}(x, a t) = (a x, t)`, `T_d` flips letter `d+1` of
`a x`, which is letter `d` of `x`, and `beta` returns the letter `a` to the second coordinate
unchanged. Hence `T_d = beta^{-d} T_0 beta^{d}` and `|T_d| <= 2d + 1`.

`T_d` is the product of the `2^d` disjoint transpositions `[w0] <-> [w1]` of the first coordinate,
`|w| = d`. It preserves all address lengths, so `c(T_d) = 0` and `T_d in ker c`; it is a
permutation of the level-`(d+1)` cubes, so it lies in `K_{d+1}`, and it moves every one of the
`2^{n(d+1)}` cubes of that level, since it flips letter `d+1` of the first coordinate of every
point. Its kernel depth is `d + 1` because it is not a permutation of level-`d` cubes.

**Step 6 (item 6).** An element `g in V` is given by a tree pair `(D_g, R_g)` with `L(g)` leaves
each. To compose `g h`, refine `R_h` and `D_g` to the smallest tree `T` containing both. A rooted
binary subtree of the infinite binary tree with `a` leaves has `a - 1` internal nodes, and the
internal nodes of `T` are the union of those of `R_h` and `D_g`, so `T` has at most
`(a - 1) + (b - 1) + 1 = a + b - 1` leaves with `a = L(h)`, `b = L(g)`. Pulling `T` back through
`h` and pushing it through `g` gives a tree pair for `g h` with at most `L(g) + L(h) - 1` leaves,
so `L(gh) <= L(g) + L(h) - 1`. Induction on a word gives `L(g) <= 1 + |g| (max_s L(s) - 1)`, linear
in `|g|`.

For `n >= 2` the corresponding refinement is of two partitions of `C^n` into bricks, and the common
refinement is a grid: the script exhibits the commuting pair `x_0 x id` and `id x x_0`, each of
brick count `3`, whose product has brick count exactly `9`. This multiplicative refinement is what
Steps 2-3 iterate.
