---
rg: 2
id: brin-thompson-nekrashevych-wp-reduction-proof
kind: route
title: Compose decorated brick tables by coordinatewise refinement and test identity bricklike in H
target: brin-thompson-nekrashevych-wp-reduces-to-self-similar-group
requires: []
---

Notation is as in the target. The one-dimensional proof is
`rover-nekrashevych-wp-reduction-proof`; this route runs it coordinatewise.

**Data.**
- Fix a finite symmetric generating set `S` of `H`. For `s ∈ S` and `x ∈ X`,
  record `s(x)` and a word `σ(s,x) ∈ S*` with `s|_x = σ(s,x)` in `H`. Let
  `c0 = max(1, max|σ(s,x)|)`.
- Write each generator of `K` as a decorated table, of depth at most `D` and
  decoration length at most `D`.

**Representation.** An element is a finite list of bricks
`((u_1, v_1, w_1), …, (u_n, v_n, w_n))`, with `u_j, v_j ∈ X*` and
`w_j ∈ S*`, meaning
`f(u_1 ζ_1, …, u_n ζ_n) = (v_1 w_1(ζ_1), …, v_n w_n(ζ_n))`.

**Refinement in coordinate `j`.** Replace a brick by the `d` bricks obtained
by changing its `j`-th entry to `(u_j x, v_j w_j(x), w_j|_x)`, for `x ∈ X`,
leaving the other entries unchanged.
- The letter and section word are computed as in the one-dimensional route, in
  time `O(|w_j|)`. The section word has length at most `c0 |w_j|`.
- Refining at a range letter `y` in coordinate `j` uses the domain letter
  `w_j^-1(y)`.

**Composition.** To compose `f` after `g`:
- **Common refinement.** Refine each range brick of `g` and each domain brick
  of `f` coordinatewise until every range brick of `g` lies in one domain brick
  of `f`. Two bricks are either disjoint or, in each coordinate, one word is a
  prefix of the other, so refining the shorter word finishes.
- **Matching.** Match `(u_j, v_j, w_j)_j` in `g` with `(v_j, q_j, w'_j)_j` in
  `f` into `(u_j, q_j, w'_j w_j)_j`.

**Bounds.** After composing `l` generators:
- every code word has length at most `D l`, so there are at most `d^{n D l}`
  bricks;
- each one-letter refinement multiplies a decoration's length by at most `c0`,
  and each composition adds two decorations. So decorations have length at most
  `(c0 + 1)^{D l} D l`.
- The list is built in time `2^{c1 l}`, with `c1` depending on `n`, `d`, `D`
  and `c0`.

**Identity test.** `f = id` iff `u_j = v_j` and `w_j = 1` in `H` for every
brick and every `j`.
- **Codes agree.** If `f = id`, the brick `Π C(u_j)` equals its image
  `Π C(v_j)`. Each `w_j` is a bijection of `X^ω`, so the image is exactly that
  product. Equal products of cones have equal factors, so `C(u_j) = C(v_j)` and
  `u_j = v_j`.
- **Decorations trivial.** Then `w_j(ζ) = ζ` for all `ζ`. A tree automorphism
  fixing every end fixes every vertex, and `H ≤ Aut(T_d)` is faithful. So
  `w_j = 1`.
- **Converse.** Immediate.

This takes at most `n d^{n D l}` word-problem calls in `H`, on words of length
at most `2^{c1 l}`, which gives `(BN1)` for a suitable `c`. ∎
