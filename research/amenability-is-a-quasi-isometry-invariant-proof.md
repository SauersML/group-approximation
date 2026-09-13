---
rg: 2
id: amenability-is-a-quasi-isometry-invariant-proof
kind: route
title: "Amenability transfers through a quasi-isometry: preimages of Følner sets are Følner sets"
target: amenability-is-a-quasi-isometry-invariant
requires: []
---

**Følner's criterion** (Følner 1955, in the thick-boundary form). For a finitely
generated group `G` with word metric `d`, write, for `A ⊆ G` and `r ≥ 0`,

```text
∂_r A = { x in G : d(x, A) <= r  and  d(x, G \ A) <= r }.
```

Then `G` is amenable iff for all `r ≥ 0` and `ε > 0` there is a finite nonempty
`A` with `|∂_r A| <= ε |A|`. Note `∂_r A ⊆ ∂_t A` for `r <= t`, and for `y ∈ A`,
`y ∈ ∂_r A` iff `d(y, G \ A) <= r`.

**Setting.** Let `f: G -> H` and `g: H -> G` be maps with, for all points,

```text
d(f x, f x') <= L d(x, x') + C,     d(g y, g y') <= L d(y, y') + C,
d(g f x, x) <= C,                   d(f g y, y) <= C.
```

**Bounded fibres.** If `f(x) = f(x')` then `d(x, x') <= d(x, gfx) + d(gfx', x') <= 2C`,
so every fibre of `f` has at most `K = |B_G(2C)|` points. Likewise every fibre of
`g` has at most `K' = |B_H(2C)|` points.

**Transfer.** Let `H` be amenable, and fix `r ≥ 0` and `ε > 0`. Put `s = Lr + C`,
`t = max(s, C)` and `δ = min(1/2, ε/(2KK'))`. Choose a finite nonempty `B ⊆ H` with
`|∂_t B| <= δ|B|`, and set `A = f^{-1}(B)`, which is finite by bounded fibres.

*Size of `A`.* Let `B° = B \ ∂_C B`, the points of `B` at distance more than `C` from
`H \ B`. For `y ∈ B°`, `f(g(y))` lies within `C` of `y`, hence in `B`, so `g(y) ∈ A`.
Since `g` has fibres of size at most `K'`,

```text
|A| >= |B°| / K' >= (|B| - |∂_t B|) / K' >= (1 - δ)|B| / K' > 0.
```

*Boundary of `A`.* If `x ∈ ∂_r A`, pick `x_1 ∈ A` and `x_2 ∉ A` within `r` of `x`.
Then `f(x_1) ∈ B`, `f(x_2) ∉ B`, and both lie within `s` of `f(x)`, so
`f(x) ∈ ∂_s B ⊆ ∂_t B`. As `f` has fibres of size at most `K`,
`|∂_r A| <= K |∂_t B| <= K δ |B|`.

*Ratio.* `|∂_r A| / |A| <= K K' δ / (1 - δ) <= 2 K K' δ <= ε`.

So `G` satisfies Følner's criterion and is amenable. ∎
