---
rg: 2
id: brin-thompson-2v-brick-count-is-exponentially-distorted
kind: claim
title: "For n >= 2 the minimal brick count of nV is exponentially distorted: an explicit word of length 3d+1 in two generators is the product of 2^d pairwise-commuting disjoint-support baker maps and needs exactly 2^(d+1) bricks; in V = 1V the leaf count is subadditive, so no such compression exists"
distinct_from:
  brin-thompson-mv-contains-a-distortion-element: that is distortion of a cyclic subgroup (the Callard--Salo element, |f^N| = O(log^4 N)); this is distortion of the brick-count filtration along a family of elements of pairwise distinct orders, and it is elementary rather than an import
  brin-thompson-nv-max-type-size-functions-are-not-cnd: that computes the brick count on a fixed Z^3 of three disjoint-support baker maps, where it is the l^inf norm; this makes the number of disjoint-support baker pieces grow exponentially in the word length, which the fixed Z^3 cannot see
  brin-thompson-triangular-subgroup-is-undistorted: that is undistortion of a subgroup in the word metric; this is distortion of a non-metric filtration (brick count), and the elements B_d used here do not lie in T_n
  thompson-f-word-length-is-comparable-to-caret-count: that is the linear comparison of word length and caret count in F; item 6 here is the corresponding statement for V, and items 2-3 show that it fails badly in nV for n >= 2
artifacts:
  - experiments/brin-thompson-cnd-2026-09-18/brick_compression.py
---

**ESTABLISHED** by `brin-thompson-2v-brick-count-exponential-distortion-proof`.

## Setting

`C = {0,1}^N`, `n >= 2`, and `nV` is Brin's group of piecewise-canonical homeomorphisms of `C^n`
on dyadic bricks. `L(g)` is the minimal number of bricks in a brick diagram of `g` (as in
`brin-thompson-nv-max-type-size-functions-are-not-cnd`). Everything below happens inside
`2V <= nV` (extend by the identity on the coordinates `3..n`).

- `beta in 2V` is the **global baker map** `(a s, t) |-> (s, a t)`, a two-brick element.
- `rho in V` swaps the first two letters, `rho(a' a t) = a a' t`, and `tau = id x rho in 2V`
  (four bricks, an involution).
- For a binary word `w`, `b_w in 2V` is the baker map supported on `[w] x C`:
  `(w a s, t) |-> (w s, a t)`, the identity off `[w] x C`. So `b_empty = beta`.
- For `d >= 0`, `B_d = prod_{|w| = d} b_w`, the product over **all** `2^d` words of length `d`.
- `sigma in V` swaps the first letter, and `T_d = beta^{-d} (sigma x id) beta^{d}`, which flips
  letter `d+1` of the first coordinate.
- `c: nV -> C(C^n, Z^n)` is the exponent cocycle, `pd` the pattern depth
  (`brin-thompson-nv-haagerup-iff-cocycle-and-kernel-domination`).

Word lengths `|.|` are taken in the two-element generating set `{beta, tau}` of the subgroup it
generates; any finite generating set of any finitely generated subgroup containing `beta` and
`tau` only changes the constants.

## Statement

1. **(the pieces)** The `2^d` maps `b_w`, `|w| = d`, have pairwise disjoint supports, hence commute
   pairwise; they are pairwise conjugate in `V x id`; and their product is
   `B_d: (w a s, t) |-> (w s, a t)` for `|w| = d`.
2. **(recursion and closed form)** `B_0 = beta`, and for `d >= 1`
   `beta B_d beta^{-1} = tau B_{d-1}`. Hence `B_d = (beta^{-1} tau)^d beta^{d+1}` and
   `|B_d| <= 3d + 1`.
3. **(exact brick count)** `L(B_d) = 2^{d+1}`. Therefore
   `log_2 L(B_d) = d + 1 >= (|B_d| - 1)/3`: the brick count grows exponentially along a family
   whose word length grows linearly. Equivalently, `L` is exponentially distorted in `nV`.
4. **(invisible to the cocycle)** `c(B_d)` is the constant `(-1, +1, 0, ..., 0)`, so
   `||c(B_d)|| = 1` and `pd(B_d) = 0`. The compression is invisible to the two cocycle
   statistics P1 and P2 of `brin-thompson-nv-a-t-menable-via-cocycle-and-kernel-domination`.
5. **(the same compression inside the cocycle kernel)** `T_d in ker c` is the product of the `2^d`
   pairwise disjoint sibling swaps `[w0] <-> [w1]`, `|w| = d`, in the first coordinate. It has
   kernel depth `d + 1`, it moves **every** level-`(d+1)` cube of `C^n` (there are `2^{n(d+1)}`
   of them), and `|T_d| <= 2d + 1`.
6. **(the contrast with `V`)** In `V = 1V` the minimal leaf count satisfies
   `L(gh) <= L(g) + L(h) - 1`, because the common refinement of two rooted binary trees with `a`
   and `b` leaves has at most `a + b - 1` leaves. Hence `L(g) <= C|g|` in `V`: no family with the
   behaviour of item 3 exists there. The difference is exactly that for `n >= 2` the common
   refinement of two brick partitions of `C^n` is a **grid** and can have `L(g) L(h)` pieces; the
   script exhibits `L((x_0 x id)(id x x_0)) = 9 = 3 * 3`.

## Why this matters

- It is the structural reason Farley's proof of the Haagerup property of `V` cannot be
  transplanted: Farley's proper cnd function on `V` is comparable to the caret (leaf) count, which
  by item 6 is comparable to word length; item 3 says the corresponding quantity on `nV` is
  exponentially distorted, and by the standard `sqrt(psi)`-subadditivity no cnd function can
  dominate it.
- It supplies the missing half of the pincer around
  `brin-thompson-nv-max-type-size-functions-are-not-cnd`: see
  `brin-thompson-nv-sum-type-size-functions-are-not-cnd`.
- It is elementary and does not use the Callard--Salo element, so it is available even if
  `callard-salo-element-is-ae-locally-periodic` stays open.

## Verification

`experiments/brin-thompson-cnd-2026-09-18/brick_compression.py` checks items 1-6 with exact
string/brick arithmetic (`experiments/brin-thompson-cnd-2026-09-17/lib2v.py`) for `0 <= d <= 8`:
the product identity of item 1, disjointness and commutation of the pieces, the closed form and
recursion of item 2, the exact guillotine DP value `L(B_d) = 2^{d+1}` of item 3, the constant
cocycle of item 4, the closed form and kernel membership of item 5, and the `V` subadditivity of
item 6 on 300 random pairs.
