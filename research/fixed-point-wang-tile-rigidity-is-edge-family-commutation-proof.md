---
rg: 2
id: fixed-point-wang-tile-rigidity-is-edge-family-commutation-proof
kind: route
title: Colour marginals turn families into face-local edge families, side-locality substitutes edge families into D-families, and two-branch edge families realise edge walls
target: fixed-point-wang-tile-rigidity-is-edge-family-commutation
requires:
  - sft-crossed-product-fp-iff-quantum-rigid
---

Lane proof (bh-g2-fixedpoint-a, 2026-09-18), not independently reviewed. Notation is as in the target. The
proof uses the following facts throughout:
- operators that commute and each lie in one commutative algebra have joint "branches";
- a sum of products over all extensions of a pattern equals the product over the pattern;
- a `D`-family is a `D'`-family for every `r <= D' <= D`. (Q2) weakens, and (Q3) on `B_(D')` is the sum
  over extensions to `B_D`, whose operators commute because `B_D` has `ℓ¹`-diameter `2D`.

## Item 1: families are edge families

Let `E` be a `D`-family, `D >= 1`. For the edge `e` between `z` and `z + e_1`, put
`P_c(e) = Σ_{right(a) = c} E_a(z)`.
- `E(z)` and `E(z + e_1)` commute, since they are at distance `1 <= 2D`.
- A mismatched domino occurs in no tiling. So by (Q3), summed over its extensions to `B_D(z)`, we get
  `E_a(z) E_b(z + e_1) = 0` when `right(a) ≠ left(b)`.
- Multiplying `Σ_{right(a)=c} E_a(z)` by `Σ_b E_b(z + e_1) = 1` therefore gives
  `P_c(e) = Σ_{left(b) = c} E_b(z + e_1)`.
- The same holds for horizontal edges, so `P` is well defined.

(F1) holds because the four edges of face `z` are functions of `E(z)`. (F2) holds, and more: since a tile
is its colours, `P_l P_r P_b P_t = E_(l,r,b,t)(z)`, which is `0` off `τ`. So `P` commutes iff `E` does.

## Item 2: substitution

**Margins of `S^k`.** Write `S^k(t)` as the array of blocks `S^(k−1)(s_q)`, with `S(t) = (s_q)`. Suppose
a site `p = q N^(k−1) + p'` lies within `m N^(k−1)` of the right side of `S^k(t)`. Then `q_1 >= N − m`.
- If `p` is not within `m N^(k−1)` of the top or bottom, then `m <= q_2 < N − m`. So `s_q` depends only on
  `right(t)`, and hence so does `p`.
- If `p` is also within that distance of the top, then `q` is a corner of `S(t)`. So `s_q`, and with it
  `p`, is constant.

The other sides are the same. So the margin of `S^k` is `M = m N^(k−1)`.

**Branches.** Let `P` be an FLEF, `F_t(Z) = P_l P_r P_b P_t`, and `M > 2D`. Then `F(Z)` is a partition of
unity by (F1) and (F2). Summing `F_t(Z)` over the tiles with `right(t) = c` gives `P_c(right edge of Z)`,
because the terms off `τ` vanish by (F2). So `E_a(z)` is:
- a function of `F(Z)` in general;
- a function of `P(e)` alone if `z` is in the margin of the side `e` of `Z`;
- a scalar if `z` is in a corner.

**(Q1)** is immediate.

**(Q2).** Take `|z − z'|_1 <= 2D`.
- *Same block:* both are functions of `F(Z)`.
- *Different blocks:* every site involved is within `2D < M` of the common boundary.
  - Across a side `e`: each site is either in the margin of `e` (a function of `P(e)`) or in a corner
    (a scalar).
  - Across a corner only: both are corners.

  They commute in all cases.

**(Q3).** All operators on `B_D(z)` commute, by (Q2).
- *One block `Z`:* the product is `Σ_t [S^k(t)|_ball = π] F_t(Z)`. Every `S^k(t)` occurs, since `τ` is
  trimmed and `S` maps tilings to tilings. So the product vanishes for every non-occurring `π`.
- *Two blocks across a side `e`:* every site is in `e`'s margin or in a corner, so the product is
  `Σ_c [pattern(c) = π] P_c(e)`.
  - If `P_c(e) ≠ 0`, some tile `t` has `right(t) = c`. That tile occurs, next to some `t'` with
    `left(t') = c`, and `S^k` of that tiling contains `pattern(c)`.
  - So the product vanishes for non-occurring `π`.
- *Three or four blocks (a corner):* every site is within `2D` of two sides of its block, so all
  operators are scalars. The resulting constant corner pattern occurs at every level-`k` grid corner.

**Commutation.** `S^k` is injective, and operators within one block commute. So
`F_t(Z) = Π_q E_(S^k(t)_q)(N^k Z + q)`. If `E` commutes, then so do all `F`, and hence all
`P_c(e) = Σ F_t`. Conversely, if `P` commutes, then every `E` is a function of commuting `F`s.

## Item 3

- *FLEFs commute ⇒ every `D`-family (`D >= 1`) commutes:* by item 1. In particular `τ` is `1`-rigid.
- *`1`-rigid ⇒ quantum rigid:* by definition.
- *`D`-rigid ⇒ every FLEF `P` commutes:* choose `k` with `m N^(k−1) > 2D`. The substituted `D`-family of
  item 2 commutes, so `P` does.
- *Finite presentation:* equivalent to quantum rigidity by `sft-crossed-product-fp-iff-quantum-rigid`.

## Item 4: edge walls (valid for any Wang set `τ`)

Let `x ≠ x'` be tilings, and call an edge *differing* if its colours in `x` and `x'` differ.
- A face lies in the difference set iff it has a differing edge, since a tile is its colours.
- The *components* are the classes of difference faces under "share a differing edge". Every differing
  edge lies in exactly one component, and every difference face lies in exactly one.

Suppose there are two components `K_1` and `K_2`. On `W = k^2`, take the idempotents `p_1 = [[1,0],[0,0]]`
and `p_2 = [[1,1],[0,0]]`, which do not commute, and set:
- `P_(x(e))(e) = 1` on edges where `x` and `x'` agree;
- `P_(x(e))(e) = p_i` and `P_(x'(e))(e) = 1 − p_i` on differing edges of `K_i`;
- `p_i = p_1` for every component other than `K_2`.

Checking the conditions:
- **(F1).** Each face uses only scalars and one pair `p_i`, `1 − p_i`.
- **(F2).** The four-edge product at a face is `p_i` on `x`'s tile, `1 − p_i` on `x'`'s tile, and `0`
  otherwise, because `p_i (1 − p_i) = 0`.
- **Non-commutation.** A differing edge of `K_1` and one of `K_2` do not commute.

Under the target's hypotheses, item 3 then gives non-rigidity at every scale.

Classically, the same pair `S^k(x)`, `S^k(x')` is a wall of width `> 2D`. No difference lies in the
margin of an agreeing side or in a corner, so the differences coming from `K_1` and from `K_2` are at
least `M > 2D` apart. Item 4 is therefore the
familiar wall certificate, read at level `0`, where it needs no width.
