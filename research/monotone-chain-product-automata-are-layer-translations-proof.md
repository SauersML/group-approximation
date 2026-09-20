---
rg: 2
id: monotone-chain-product-automata-are-layer-translations-proof
kind: route
title: Fix the constants, cut out one layer over constant backgrounds of the others, and sandwich it between the all-bottom and all-top slices
target: monotone-chain-product-automata-are-layer-translations
requires:
  - monotone-injective-chain-automata-are-translations
---

Complete proof. Automata act by `ρ(x)(h) = μ((x(hm))_{m ∈ M})` with a finite memory `M`. Write `L = ∏_i C_i`,
`π_i` for the projections, `0_i` and `1_i` for the bottom and top of `C_i`. Factors with `|C_i| = 1` carry no
information, so assume `|C_i| >= 2` for every `i`. Order configurations sitewise.

## Step 0. A power fixing constants

`ρ` sends each constant `c^G` to a `G`-invariant configuration, which is a constant. It is injective and monotone,
so it induces an injective, hence bijective, monotone self-map `α` of the finite poset `L`. A monotone bijection of
a finite poset is an automorphism: it maps the finite set of comparable pairs injectively into itself, hence onto
it. So `α` has finite order `N`, and `ρ^N` fixes every constant. `ρ^N` is again a monotone injective automaton.
Replace `ρ` by `ρ^N` and `μ` by its rule. From now on `ρ(c^G) = c^G` for every `c ∈ L`.

## Step 1. Layer bounds

Let `y ∈ L^M` and `i` be fixed, and let `c = max_m π_i y(m)` in the chain `C_i`. Let `z ∈ L` have `π_i z = c` and
`π_j z = 1_j` for `j != i`. Then `y(m) <= z` for all `m`, so monotonicity and `ρ(z^G) = z^G` give `μ(y) <= z`, that
is `π_i μ(y) <= c`. The dual argument with the minimum and the bottoms gives

    min_m π_i y(m)  <=  π_i μ(y)  <=  max_m π_i y(m).                              (1)

## Step 2. Slices are chains acted on by translations

Fix `i` and a tuple `e = (e_j)_{j != i}` with `e_j ∈ C_j`. Let `Z_e` be the set of `x ∈ L^G` with `π_j x(g) = e_j`
for all `g` and all `j != i`. By (1) applied to each `j != i`, `ρ(Z_e) ⊆ Z_e`. The map `x -> π_i ∘ x` is an order
isomorphism from `Z_e` onto `C_i^G` commuting with the shift. So `ρ` restricted to `Z_e` is a monotone injective
automaton on the chain `C_i`, with rule `ν_e(w) = π_i μ(w, e)`, where `(w, e)` is the pattern with layer `i` equal
to `w ∈ C_i^M` and layer `j` constant `e_j`.

By `monotone-injective-chain-automata-are-translations` it is a copy of one coordinate: there is `t_i(e) ∈ G` with
`π_i ρ(x)(h) = π_i x(h t_i(e))` for all `x ∈ Z_e` and `h`. Since `ρ(x)(h)` depends only on `x|_{hM}` and `C_i` has
two letters, `t_i(e) ∈ M`. So `ν_e(w) = w(t_i(e))` for every `w ∈ C_i^M`.

## Step 3. The sandwich

Let `b` be the tuple of bottoms `(0_j)_{j != i}` and `u` the tuple of tops `(1_j)_{j != i}`. Put `s = t_i(b)` and
`s' = t_i(u)`. For `y ∈ L^M` with layer `i` equal to `w`, we have `(w, b) <= y <= (w, u)` sitewise. Monotonicity of
`μ` gives

    w(s) = π_i μ(w, b)  <=  π_i μ(y)  <=  π_i μ(w, u) = w(s').                      (2)

If `s != s'`, take `w` with `w(s) = 1_i` and `w(s') = 0_i`. Then (2) says `1_i <= 0_i`, false since
`|C_i| >= 2`. So `s = s'`, and (2) gives `π_i μ(y) = w(s) = π_i y(s)`. Put `t_i = s`.

## Step 4. Conclusion

Doing this for every `i` gives `μ(y) = (π_i y(t_i))_i`, that is `ρ(x)(h) = (π_i x(h t_i))_i`. This map is bijective,
with inverse `x -> (h -> (π_i x(h t_i^{-1}))_i)`. So the original `ρ^N` is bijective. Then the original `ρ` is
surjective, since its image contains the image of `ρ^N`, and it is injective by hypothesis. This proves both items.

## Remarks

- Only Step 2 uses the chain theorem. For Boolean lattices (`|C_i| = 2`) it can be replaced by
  `monotone-binary-injective-rules-are-copies`, and the proof is then purely local.
- Steps 1 and 3 use only that `L` is a product and that each factor has a bottom and a top. They do not use
  injectivity.
- The translations `t_i` can differ between factors. The automorphism `α` of Step 0 can permute isomorphic factors,
  which is why a power is needed.
