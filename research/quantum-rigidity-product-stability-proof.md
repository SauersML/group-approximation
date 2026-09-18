---
rg: 2
id: quantum-rigidity-product-stability-proof
kind: route
title: The constancy rules make each factor's letter projections constant along the other factor, so a product family splits into two factor families that commute at every common site
target: quantum-rigidity-is-product-stable
requires:
  - fp-v-times-subshift-full-groups-force-quantum-rigidity
---

Notation as in the target. Write `Z = X ⊠ Y`, and `B_D(p)` for the ball of radius `D` about `p`
in `Λ`. Its diameter is `2D`.

## Step 0. Expansion inside a ball

Let `(E_c(p))` be a `D`-quantum family for `Z`, with `c ∈ A × B`. By (Q2), all `E_c(q)` with
`q ∈ B_D(p)` commute. So for any sites `q_1, …, q_m ∈ B_D(p)` and letters `c_1, …, c_m`, (Q1)
gives the expansion

```text
E_(c_1)(q_1) ⋯ E_(c_m)(q_m) = Σ_π ∏_(f ∈ B_D(p)) E_(π(f))(f),
```

summed over the patterns `π` on `B_D(p)` with `π(q_i) = c_i`. By (Q3), only patterns
occurring in `Z` contribute.

## Step 1. Item 1: finite type

The first rule and connectivity of the Cayley graph of `Λ_2` make `x̃` constant on each coset
`{g} × Λ_2`. So `x̃(g,h) = x(g)`, and the third rule puts `x` in `X`. The same holds for `ỹ`.
Conversely every `(x̃, ỹ)` of the displayed form obeys all four rules.

## Step 2. Item 2: dynamics

`Stab(x, y) = Stab(x) × Stab(y)`, and the orbit of `(x, y)` is the product of the two
orbits. Orbits are dense in `X × Y` iff they are dense in both factors.

## Step 3. Splitting a product family

Put `E^1_a(p) = Σ_b E_(a,b)(p)` and `E^2_b(p) = Σ_a E_(a,b)(p)`.
- These are partitions of unity, and they commute at a common site.
- By orthogonality of the `E_c(p)`, `E^1_a(p) E^2_b(p) = E_(a,b)(p)`.

**Constancy.** Let `s ∈ S_2`, `a ≠ a'` and `p = (g,h)`. Every pattern on `B_D(p)` (with
`D ≥ 1`) with first coordinate `a` at `(g,h)` and `a'` at `(g,hs)` breaks the first rule, so
it does not occur. By Step 0, `E^1_a(g,h) E^1_(a')(g,hs) = 0`. Hence

```text
E^1_a(g,h) = E^1_a(g,h) Σ_(a'') E^1_(a'')(g,hs) = E^1_a(g,h) E^1_a(g,hs),
```

and symmetrically `E^1_a(g,hs) = E^1_a(g,hs) E^1_a(g,h)`. The two sites are at distance 1, so
these operators commute, and `E^1_a(g,h) = E^1_a(g,hs)`. By connectivity of `Λ_2`,
`E^1_a(g,h) = F_a(g)` does not depend on `h`. Likewise `E^2_b(g,h) = G_b(h)`.

## Step 4. The factor families

`(F_a(g))_(a ∈ A, g ∈ Λ_1)` is a `D`-quantum family for `X` over `Λ_1`.
- (Q1) holds by Step 3.
- (Q2): for `d_1(g,g') ≤ 2D`, `F(g) = E^1(g,h)` and `F(g') = E^1(g',h)` sit at sites at
  distance `≤ 2D`.
- (Q3): let `α` be a pattern on `B^1_D(g)` that does not occur in `X`. Every pattern `π` on
  `B_D((g,h))` whose first coordinates restrict to `α` on `B^1_D(g) × {h}` does not occur in
  `Z`. If it did, `x̃` would be constant in the `Λ_2` direction and `α` would occur in `X`.
  By Step 0, `∏ F_(α(f))(gf) = ∏ E^1_(α(f))(gf, h) = 0`.

Similarly `(G_b(h))` is a `D`-quantum family for `Y` over `Λ_2`.

## Step 5. Item 3, forward

Assume `X` and `Y` are `D`-rigid.
- The `F_a(g)` commute with each other, and the `G_b(h)` commute with each other.
- `F_a(g)` and `G_b(h')` commute, since `F_a(g) = E^1_a(g,h')` and `G_b(h') = E^2_b(g,h')`
  live at the common site `(g,h')`.

Hence every `E_(a,b)(g,h) = F_a(g) G_b(h)` commutes with every other.

## Step 6. Item 3, converse

Let `(F_a(g))` be a `D`-quantum family for `X` over `Λ_1` on `W`. Fix `y ∈ Y` and put
`E_(a,b)(g,h) = [y(h) = b] F_a(g)`, with `[·] ∈ {0, 1}` scalars.
- (Q1) and (Q2) are inherited from `(F_a(g))`.
- (Q3): let `π = (π_1, π_2)` be a pattern on `B_D((g,h))` that does not occur in `Z`. Write
  `α = π_1` restricted to the row `B^1_D(g) × {h}`. Since `F_a(g')` does not depend on the second
  coordinate and the factors commute inside the ball, the product of `π` equals the product of
  the scalars `[y(h') = π_2(g',h')]` times `∏_(sites) F_(π_1(site))`. One of three cases applies.
  - `π_1` changes along some `Λ_2`-edge `(g', h'), (g', h's)` of the ball. The product then
    contains `F_a(g') F_(a')(g')` with `a ≠ a'`, which is `0`.
  - `π_1` is constant along `Λ_2`-edges. Every point `(gf, hk)` of the ball joins the row
    `Λ_1 × {h}` by `Λ_2`-edges inside the ball, so `π_1(gf, hk) = α(f)`. The `F`-part of the
    product is then `∏_(f ∈ B^1_D(g)) F_(α(f))(gf)`, using idempotency. If `α` does not occur
    in `X`, this vanishes by (Q3) for `X`.
  - `π_1` is constant and `α` occurs in `X`, say `α = x|_(B^1_D(g))`. Then `π_2` is not the
    restriction of `ỹ(·,·) = y(·)`: otherwise `π` is the restriction of `(x̃, ỹ) ∈ Z`. So some
    scalar factor vanishes.

The family is noncommuting if `(F_a(g))` is. So `D`-rigidity of `Z` forces that of `X`, and
symmetrically that of `Y`.

## Step 7. Item 4, rings

`LC(X × Y, k) = LC(X, k) ⊗ LC(Y, k)` (locally constant functions on a product of Cantor spaces),
and the action of `Λ_1 × Λ_2` is the tensor product of the two actions. Crossed products by a
direct product of commuting actions on tensor factors are tensor products of the crossed
products. The tensor product of two finitely presented `k`-algebras is presented by the union of
the two presentations and the commutation of the two generating sets, so it is finitely
presented.
