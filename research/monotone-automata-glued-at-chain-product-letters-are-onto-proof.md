---
rg: 2
id: monotone-automata-glued-at-chain-product-letters-are-onto-proof
kind: route
title: Split each defect into its meet and its join with the glue letter, charge both halves by layer counts, and close with charge noncreation
target: monotone-automata-glued-at-chain-product-letters-are-onto
requires:
  - monotone-chain-product-automata-are-layer-translations
  - finite-injective-charge-noncreation-forces-surjectivity
---

Complete proof. Notation as in the target. `ρ` has a finite memory `M`, and configurations are ordered sitewise.
Call `x` *finite* if `S(x) = {g : x(g) != c}` is finite.

## Step 0. A power fixing constants

As in Step 0 of `monotone-chain-product-automata-are-layer-translations-proof`, `ρ` permutes the constants by an
automorphism of the finite poset `L`. So some power `τ = ρ^N` fixes every constant. `τ` is monotone and injective.
If `τ` is surjective then so is `ρ`, because `τ(L^G) ⊆ ρ(L^G)`. So it suffices to prove that `τ` is surjective.

## Step 1. The two sides are invariant and rigid

If `x <= c^G` then `τ(x) <= τ(c^G) = c^G`. So `τ` maps `(↓c)^G` into itself, and dually `(↑c)^G`. The restrictions
are monotone injective automata on the posets `↓c` and `↑c`, and they fix every constant.

Fix an order isomorphism `↓c ≅ ∏_{i=1..p} A_i` with finite chains `A_i`. It sends `c`, the top of `↓c`, to the tuple
of tops. By `monotone-chain-product-automata-are-layer-translations` (item 1, with power `1` since constants are
already fixed), there are `t_i ∈ G` with `π_i τ(z)(h) = π_i z(h t_i)` for all `z ∈ (↓c)^G`. Dually, fix
`↑c ≅ ∏_{j=1..q} B_j`, sending `c` to the tuple of bottoms. There are `u_j ∈ G` with
`π_j τ(z)(h) = π_j z(h u_j)` for all `z ∈ (↑c)^G`.

## Step 2. The side charges are exact

For `d ∈ ↓c` put `w_-(d) = #{i : π_i d != top of A_i}`. For `d ∈ ↑c` put `w_+(d) = #{j : π_j d != bottom of B_j}`.
- `w_-` is antitone on `↓c` and vanishes only at `c`.
- `w_+` is monotone on `↑c` and vanishes only at `c`.

For finite `z ∈ (↓c)^G`, Step 1 gives `{h : π_i τ(z)(h) != top} = {g : π_i z(g) != top} t_i^{-1}`. Summing over `i`:

    Σ_h w_-(τ(z)(h)) = Σ_g w_-(z(g)).                                             (1)

The same holds for `w_+` on finite `z ∈ (↑c)^G`.

## Step 3. The glued charge never grows

Define `w(d) = w_-(d ∧ c) + w_+(d ∨ c)` for `d ∈ L`, using (a). Then `w(d) = 0` iff `d ∧ c = c` and `d ∨ c = c`,
that is iff `d <= c` and `d >= c`, that is iff `d = c`. So `w` is a positive charge on `L \ {c}` and vanishes at `c`.
For finite `x` put `W(x) = Σ_g w(x(g))`.

Let `x` be finite, and put `x_-(g) = x(g) ∧ c` and `x_+(g) = x(g) ∨ c`. Then `x_- ∈ (↓c)^G` and `x_+ ∈ (↑c)^G` are
finite, `x_- <= x <= x_+`, and `W(x) = Σ_g w_-(x_-(g)) + Σ_g w_+(x_+(g))`.

Fix `h`. Monotonicity gives `τ(x_-)(h) <= τ(x)(h)`, and `τ(x_-)(h) <= c` by Step 1. So `τ(x_-)(h)` is a lower bound
of `τ(x)(h)` and `c`, and
`τ(x_-)(h) <= τ(x)(h) ∧ c`. Since `w_-` is antitone, `w_-(τ(x)(h) ∧ c) <= w_-(τ(x_-)(h))`. Dually,
`τ(x)(h) ∨ c <= τ(x_+)(h)` and `w_+(τ(x)(h) ∨ c) <= w_+(τ(x_+)(h))`. Summing over `h` and using (1) on both sides:

    W(τ(x)) <= Σ_h w_-(τ(x_-)(h)) + Σ_h w_+(τ(x_+)(h)) = Σ_g w_-(x_-(g)) + Σ_g w_+(x_+(g)) = W(x).      (2)

## Step 4. Charge noncreation

`τ` is a cellular automaton on `L^G` fixing `c^G`. It is injective, hence injective on finite configurations. Every
letter other than `c` has positive charge `w`, and by (2) `W(τ(x)) <= W(x)` for every finite `x`. By
`finite-injective-charge-noncreation-forces-surjectivity`, with distinguished symbol `c`, equality holds for every
finite `x` and `τ` is surjective on `L^G`. By Step 0, `ρ` is surjective. The equality is the stated conservation
of `W`.

## Remarks

1. **Why both halves.** A letter `d` incomparable with `c` has `d ∧ c < c < d ∨ c`, so its defect is seen on both
   sides. The chain proof charges each defect once, which works only when every letter is comparable with the split
   level. The sum `w_- + w_+` charges such a defect by its side counts, and (2) then compares the two sides
   separately.
2. **The V shape** `{0 < a, 0 < b}` (sketch, not landed). It fails (a) at every letter. After fixing constants, the
   covers `0 ⋖ a` and `0 ⋖ b` give copies of `t` and `t'` (item 3 of `monotone-strict-automata-ascend-along-poset-homs`).
   Take a pattern with `a` at `t`, `b` at `t'` and `0` elsewhere. Its value lies above `a` and above `b`, which is
   impossible, so `t = t'`. Every pattern `y` is then pinned: `y(t) ∈ {a, b}` forces the value `y(t)` from below, and
   `y(t) = 0` forces the value below both `a` and `b` from above, by filling `t` with `a` or with `b`. So the rule is
   `y(t)`, a copy. How far this local sandwich extends to other posets without joins, such as fences, is not
   checked.
3. **Iteration.** Gluing needs, on each side, a charge that is exact or nonincreasing at the glue letter. This
   theorem supplies surjectivity and conservation of `W` at `c`, but no such charge at the extreme backgrounds of
   `L`, so it does not iterate. When `L` is a lattice, a cover-by-cover lower bound does hold at the top background: for a coatom `k` with
   copy `s_k` on `{k, 1}^G`, `{h : τ(x)(h) <= k} ⊇ {g : x(g) <= k} s_k^{-1}`. That bound is a nondecrease, the wrong
   direction for charge noncreation.
