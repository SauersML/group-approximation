---
rg: 2
id: path-folded-sft-rigidity-pullback-proof
kind: route
title: Pull a fibre quantum family back along the fold with scalar skeleton idempotents; Lipschitz carries commutation, folds in Z carry the forbidden patterns, surjectivity carries noncommutation
target: path-folded-sfts-are-quantum-rigid-only-if-the-fibre-is
requires:
  - fp-v-times-subshift-full-groups-force-quantum-rigidity
---

Notation as in the target: `Λ`, `Λ'`, `X ⊆ A^(Λ')`, `Z ⊆ (A × B)^Λ`, the skeleton `y ∈ B^Λ`, and a
1-Lipschitz surjection `β: Λ → Λ'` with `x∘β ⊗ y ∈ Z` for all `x ∈ X`. Balls `B_D` are taken in the
respective word metrics, and `Z` has forbidden patterns inside `B_D`.

## The pulled-back family

Let `F_a(z)` (`a ∈ A`, `z ∈ Λ'`) be a `D`-quantum family for `X` on a `k`-space `W`. Put

```text
E_(a,b)(g) = [b = y(g)] · F_a(β(g))      (a ∈ A, b ∈ B, g ∈ Λ),
```

where `[·]` is `1` or `0`.

**(Q1).** At `g`, the nonzero members are `F_a(β(g))` for `a ∈ A`, attached to `b = y(g)`. These
are orthogonal idempotents summing to `I`.

**(Q2).** Let `d(g, g') <= 2D`. Then `d(β(g), β(g')) <= 2D`, so `F_a(β(g))` and `F_(a')(β(g'))`
commute. Scalars commute with everything.

**(Q3).** Let `α` be a pattern on `B_D`, written `α(f) = (α_A(f), α_B(f))`, such that no point of
`Z` has pattern `α` at `p`, i.e. on `pB_D`. Let `Π` be the product of `E_(α(f))(pf)` over
`f ∈ B_D`, in any order.
- If `α_B(f) ≠ y(pf)` for some `f`, then `Π` contains the scalar `0`.
- Otherwise `Π` is a product of the `F_(α_A(f))(β(pf))`. These all commute, since
  `β(pB_D) ⊆ B_D(β(p))` has diameter `<= 2D`.
  - If two `f, f'` with `β(pf) = β(pf')` get different letters, `Π` contains
    `F_a(z) F_(a')(z) = 0`.
  - Otherwise `Π = ∏_(u ∈ U) F_(γ(u))(u)`, where `U = β(pB_D)` and `γ(β(pf)) = α_A(f)`.
- **`γ` does not occur in `X`.** If some `x ∈ X` had `x|_U = γ`, then `x∘β ⊗ y ∈ Z` would have
  pattern `α` at `p`, contrary to the choice of `α`.
- **So `Π = 0`.**
  - By (Q1) and commutation on the ball `B_D(β(p))`,
    `∏_(u∈U) F_(γ(u))(u) = Σ_δ ∏_(u ∈ B_D(β(p))) F_(δ(u))(u)`.
  - The sum is over all patterns `δ` on `B_D(β(p))` extending `γ`.
  - No `δ` occurs in `X`, so each summand vanishes by (Q3) for `F`.

So `E` is a `D`-quantum family for `Z` on `W`.

## Transferring noncommutation

Suppose `F_a(z)` and `F_(a')(z')` do not commute. Pick `g ∈ β^(-1)(z)` and `g' ∈ β^(-1)(z')`,
using surjectivity. Then `E_(a, y(g))(g) = F_a(z)` and `E_(a', y(g'))(g') = F_(a')(z')` do not
commute. So if `Z` is `D`-rigid, every `D`-family of `X` commutes, and `X` is `D`-rigid. ∎

## The ABHT instance

In arXiv:2204.11492v3, Proposition `configsJuntas` (TeX l.626ff), the configurations of their `Z`
are exactly `x ⊗ y: w t^i ↦ (x_(i, j), y_w)` with `x ∈ X`, `y ∈ Y_f`, and
`j = 2 max{|w'| : w' ⊑ w, w' ⊑ W(y)} − |w|`. Fix any `y` and put `β(w t^i) = (i, j)`.

- **1-Lipschitz for `ℓ^1` on `Z^2`, hence for every standard metric there.**
  - Multiplying by `t^(±1)` changes `i` by 1 and fixes `j`.
  - Multiplying by a tree generator changes `j` by exactly `±1`. This is checked in their proof of
    `configsJuntas`, both when the step follows the flow and when it goes against it.
- **Onto.** `j(ρ_W(m)) = m` for `m >= 0` and `j = m` along `W_0^m` for `m < 0`, where `ρ_W` is their
  path function. So every `(i, m)` is hit.

The lemma applies. ∎
