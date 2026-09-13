---
rg: 2
id: fpbs-spectral-margin-product-move-proof
kind: route
title: Expansion bounds p_c, walk counting bounds p_u, and one generator pair moves the margin by at most 2
target: fpbs-spectral-margin-survives-product-generator-moves
requires:
  - fpbs-expansion-thinning-threshold
  - fpbs-cluster-count-trichotomy
artifacts:
  - research/artifacts/fpbs-single-product-move-2026-09-12.md
---

Notation as in the target, with `d = |S|` and `A_S f(x) = sum_{s ∈ S} f(xs)`.
Sections 3–4 of the artifact carry the same proof in more detail.

1. **Walk counting.** Every open path is a walk, so
   `tau_p(e,g) <= sum_{l >= 0} p^l A_S^l(g,e)`. If `p ||A_S|| < 1`, the series
   converges in operator norm, and `tau_p(e, .)` lies in `l2(Gamma)`.
2. **`p_u(S) >= 1/||A_S||`.** Let `p > p_u`.
   - `p > p_c` gives `theta(p) > 0`.
   - `fpbs-cluster-count-trichotomy`, item 2, gives a unique infinite cluster.
   - By Harris–FKG and uniqueness, `tau_p(e,g) >= theta(p)^2` for every `g`.
   - `Gamma` is infinite, so `tau_p(e, .)` is not in `l2`, and step 1 forces
     `p ||A_S|| >= 1`.

   Let `p` decrease to `p_u`.
3. **Item 1.** `||A_S delta_e||^2 = d`, so `||A_S|| >= 1`, and `m(S) > 0` forces
   `h(S) > 0`. Then:
   - `fpbs-expansion-thinning-threshold` gives `p_c(S) <= 1/(1+h(S))`;
   - `m(S) > 0` gives `1/(1+h(S)) < 1/||A_S||`;
   - step 2 gives `1/||A_S|| <= p_u(S)`.
4. **Item 4.** For finite `F`,
   `<A_S 1_F, 1_F> = sum_{x ∈ F} #{s : xs ∈ F} = d|F| - |∂_E F|`, since a
   boundary edge `{x,y}` with `x ∈ F` is counted once, by the label `x^{-1}y`.
   So `h(S) >= d - ||A_S||` and `m(S) >= 1 + d - 2||A_S||`. Finally
   `||A_S|| = d rho(S)`, because conjugating by `f ↦ f∘inv` turns `A_S` into
   `sum_{s ∈ S} lambda(s)`.
5. **Adding a pair.** If `t ∉ S ∪ {e}`, then `t^{-1} ∉ S`. So `A_{S+}` is `A_S`
   plus the unitaries `f ↦ f(. t)` and `f ↦ f(. t^{-1})`, one unitary if
   `t^2 = e`, and `||A_{S+}|| <= ||A_S|| + 2`. `Cay(Gamma,S)` is a spanning
   subgraph of `Cay(Gamma,S+)`, so every edge boundary only grows and
   `h(S+) >= h(S)`. Hence `m(S+) >= m(S) - 2`.
6. **Removing a pair.**
   - `0 <= A_{S-} <= A_S` entrywise, so
     `|<A_{S-} f, g>| <= <A_S |f|, |g|>`, and `||A_{S-}|| <= ||A_S||`.
   - A boundary edge of `F` that is removed is `{x, xt}` or `{x, xt^{-1}}` for
     its endpoint `x ∈ F`. So at most `2|F|` boundary edges disappear, and
     `h(S-) >= h(S) - 2`.
   - Hence `m(S-) >= m(S) - 2`. This proves item 2.
7. **Item 3.** By item 2, `m(S_j) >= m(S_0) - 2j > 2(k-j) >= 0`, and item 1
   applies to each `S_j`. With `k = 1` and `S_0 = S`, this gives the gap at `S`
   and after any Add or Remove move of
   `fpbs-gap-survives-product-generator-moves`.
