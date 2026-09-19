---
rg: 2
id: short-expander-subgroups-force-folner-growth-proof
kind: route
title: Split a Følner set along right cosets of the finite subgroup and average the Cheeger inequality over the cosets
target: short-expander-subgroups-force-folner-growth
requires: []
---

Notation as in the claim. No imports.

## Step 1. Long elements move Følner sets a little

Let `Ω` satisfy `|Ω \ xΩ| <= |Ω|/n` for all `x in S`.
- For `x in S`, `|Ω \ x^(−1)Ω| = |xΩ \ Ω| = |Ω| − |Ω ∩ xΩ| = |Ω \ xΩ|`, since
  `|xΩ| = |Ω|`. So the bound holds for `x in S ∪ S^(−1)`.
- For `g, g'` in `H`,
  `Ω \ gg'Ω ⊂ (Ω \ gΩ) ∪ (gΩ \ gg'Ω) = (Ω \ gΩ) ∪ g(Ω \ g'Ω)`.
- By induction on length, `|Ω \ yΩ| <= |y|_S · |Ω|/n` for every `y in H`.

## Step 2. Coset splitting (item 1)

Let `Γ`, `T`, `L`, `δ` be as in item 1, and let `Ω` be a finite nonempty set with
`|Ω \ xΩ| <= |Ω|/n` for `x in S`, where `n >= 2|T|L/δ`.
- `H` is the disjoint union of right cosets `Γg`. Fix a set `R` of coset
  representatives. For `g in R` put `A_g = (Ω ∩ Γg) g^(−1) ⊂ Γ`. Then
  `Σ_g |A_g| = |Ω|`.
- For `y in Γ`, left multiplication by `y` preserves each coset `Γg`. So
  `(Ω \ yΩ) ∩ Γg = (Ω ∩ Γg) \ y(Ω ∩ Γg)`, and right multiplication by `g^(−1)`
  carries this onto `A_g \ yA_g`. Hence
  `|Ω \ yΩ| = Σ_g |A_g \ yA_g|`.
- Sum over `y in T` and use Step 1 with `|y|_S <= L`:

  ```text
  Σ_g Σ_(y in T) |A_g \ yA_g|  <=  |T| L |Ω| / n  <=  δ |Ω| / 2.
  ```

- Call `g` *small* if `0 < |A_g| <= |Γ|/2`. For small `g` the Cheeger bound gives
  `Σ_(y in T) |A_g \ yA_g| >= δ |A_g|`. All terms are nonnegative, so
  `δ Σ_(small g) |A_g| <= δ|Ω|/2`, that is `Σ_(small g) |A_g| <= |Ω|/2`.
- Since `Ω` is nonempty, `Σ_g |A_g| = |Ω| > |Ω|/2`, so some `g` with `A_g`
  nonempty is not small: `|A_g| > |Γ|/2`. Then `|Ω| >= |A_g| > |Γ|/2`.

Every set admissible in the definition of `F_(H,S)(n)` therefore has more than
`|Γ|/2` elements, which is item 1. (Amenability of `H` is used only to know that
`F_(H,S)(n)` is finite; the inequality holds for any group.)

## Step 3. Profile form (item 2)

Take `Γ, T` realizing `X^δ_(H,S)(L)`. Then `|T| <= L`, so `2|T|L/δ <= 2L^2/δ`,
and item 1 at `n = ⌈2L^2/δ⌉` gives `F_(H,S)(n) > |Γ|/2`. For the trivial group
the claim is `F >= 1 > 1/2`.

## Step 4. Monotonicity (item 3)

If `Γ ≤ K` is finite with symmetric generating set `T`, `|T| <= L`,
`|y|_R <= L` and `h(Γ,T) >= δ`, then `|y|_S <= c|y|_R <= cL` and
`|T| <= L <= cL`. The Cheeger constant depends only on `(Γ,T)`. So `(Γ,T)`
counts for `X^δ_(H,S)(cL)`. The same argument without the Cheeger condition
gives the `FS` inequality.

## Step 5. Transfer (item 4)

Write `X = X^δ_(H,S)` and `F = F_(H,S)`. Let `C >= 1`. Put `K = ⌈2/δ⌉ + 1` and
`C' = 2CK`. By hypothesis there is `L` with `X(L) > C' U'(C'L)`.
- `X(L) >= 2`, so `L >= 1`. Put `n = ⌈2L^2/δ⌉ <= (2/δ + 1)L^2 <= K L^2`.
- `U'(C'L) = C'L · U(C'^3 L^3) >= U(C'^3 L^3)`, and `C' >= 2C`, so
  `X(L)/2 > C U(C'^3 L^3)`.
- `C n <= C K L^2 <= C'^3 L^3`, and `U` is non-decreasing, so
  `U(C'^3 L^3) >= U(Cn)`.
- By item 2, `F(n) > X(L)/2 > C U(Cn)`.

So for every `C` some `n` has `F(n) > C U(Cn)`, which is `F ⋠ U`. The relation
`⋠` does not depend on the finite generating set. `∎`

## Remark (the Brieussel--Zheng witnesses)

In `Δ_U` of `decidable-amenable-groups-have-no-recursive-folner-bound`, with
generating tuple `T` of (BZ1) there, fix `t >= 1`. The elements `α_a` (`a in A`)
and `τ^(−k_t) β_b τ^(k_t)` (`b in B`) have length at most `2k_t + 1`. In the
factor `Δ_s` they are the lamps `a(s)δ_0` and `b(s)δ_(k_s − k_t)`. For `s = t`
they generate `Γ_(t) δ_0 ≅ Γ_(t)`. For `s ≠ t` the two positions differ
(`k_s` is strictly increasing and `k_0 = 0`), so they generate `A × B`. Hence
they generate a finite subgroup `Q_t ≤ Δ_U` that surjects onto `Γ_(t)`, so
`|Q_t| >= |Γ_(m_t)| > t U(t^2 k_t)`. This shows `FS_(Δ_U) ⋠ U`, which is used in
`higman-thompson-finite-subgroup-profile-is-recursive`. With the property (T)
Cheeger bound of (BZ2) there, `Q_t` is also a uniform expander on these
generators, so the Følner lower bound of `Δ_U` is an instance of item 1. That
second sentence is not needed anywhere and is not checked here.
