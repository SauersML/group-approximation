---
rg: 2
id: two-cell-ab-nonzero-admissible-needs-g-in-conj-closure-proof
kind: route
title: Push the unimodular cylinder row to the permutation module Z[P\G], on which <g> acts freely modulo P, and use that eps a T - b with consecutive nonzero coefficients is never a unit of a nontrivial cyclic group ring
target: two-cell-ab-nonzero-admissible-needs-g-in-conj-closure
requires:
  - two-cell-core-deletions-need-a-unit-fox-coefficient
  - core-relation-elimination-bounds-relative-defect
artifacts: []
---

Notation is as in the claim. `∂_x u_j ∈ ZH` is evaluated in `ZG`, and its augmentation is the
`x`-coordinate of `[u_j]`, that is, `α_x` for `j = 0` and `β_x` for `j = 1`.

## Step 1: push to the permutation module

Suppose `Σ_x c_x d_x = 1` in `ZG` (the right-coefficient convention of (U2)). The coset map
`π: ZG → Z[P\G]`, `γ ↦ Pγ`, is a map of right `ZG`-modules. So

`Σ_x π(c_x) d_x = P`.

Two facts compute `π(c_x)`:
- For `h ∈ H ⊆ P` we have `P h = P`. So `π(∂_x u_1) = β_x · P`.
- For `h ∈ H` we have `P g h = P (g h g^{-1}) g = P g`, because `g H g^{-1} ⊆ P`. So
  `π(g ∂_x u_0) = α_x · Pg`.

Hence `π(c_x) = ε α_x Pg - β_x P`.

## Step 2: the free action of g

Since `g P g^{-1} = P`, the rule `ḡ · Pγ = P g γ` defines a left action of `⟨g⟩` on `P\G`. It
commutes with the right `G`-action. Its stabilizers are trivial modulo `P ∩ ⟨g⟩`: `P g^k γ = P γ`
iff `g^k ∈ P`. So `Q = ⟨g⟩/(⟨g⟩ ∩ P)` acts freely.

Hence `Z[P\G]` is a free left `ZQ`-module, with one basis element for each `Q`-orbit, and right
multiplication by `ZG` is `ZQ`-linear. In this notation `Pg = ḡ · P` and
`π(c_x) = (ε α_x ḡ - β_x) · P`. Step 1 becomes

`Σ_x (ε α_x ḡ - β_x) · (P d_x) = 1 · P`.

Project onto the free summand `ZQ · P`, the orbit of `P`. Let `z_x ∈ ZQ` be the coefficient of `P`
in `P d_x`. The projection is `ZQ`-linear, so

`Σ_x (ε α_x ḡ - β_x) z_x = 1` in `ZQ`.

This proves (N1).

**Other convention.** If unimodularity is read as `Σ_x d_x c_x = 1`, use left cosets `γP` with the
right action `γP · ḡ = γ g P`, which is again free modulo `P`. Then
`c_x P = (ε α_x g - β_x) P`, because `∂_x u_j ∈ ZH` and `H ⊆ P`. The same projection gives
`Σ_x z_x (ε α_x ḡ - β_x) = 1`. Since `ZQ` is commutative, the conclusion is the same.

## Step 3: rank one

With `α = a p` and `β = b p`, (N1) says

`(ε a ḡ - b) · Σ_x p_x z_x = 1`.

So `u = ε a ḡ - b` is a unit of `ZQ`. Put `A = εa`. Applying the augmentation gives `A - b = ±1`
(this is the degree-one relation). Since `a b ≠ 0`, the integers `A` and `b` are nonzero and differ
by 1, so they have the same sign and `A b > 0`.

- **`Q` infinite.** Then `ZQ = Z[T^{±1}]`. Its units are `±T^k`, and `A T - b` has two nonzero
  coefficients. So it is not a unit, a contradiction.
- **`Q` finite of order `m ≥ 2`.** Multiplication by `u` on `ZQ ≅ Z^m` has determinant
  `N(u) = Π_{ζ^m = 1} (A ζ - b)`, and this is `±1` for a unit. For `ζ = 1` the factor has absolute
  value `|A - b| = 1`. For `ζ ≠ 1`,

  `|A ζ - b|^2 = A^2 + b^2 - 2 A b Re ζ > A^2 + b^2 - 2 A b = 1`,

  because `A b > 0` and `Re ζ < 1`. So `|N(u)| > 1`, a contradiction.

Hence `Q = 1`, that is, `g ∈ P`. This proves (N2).

**Consequences.**
- `P ⊆ ⟨⟨H⟩⟩`, which gives the normal-closure statement.
- If `g` normalizes some `P' ⊇ H`, then `P ⊆ P'`, so `g ∈ P'`. Taking `P' = H` contradicts
  `g ∉ H`, which is (U1).
- For a quotient `π`, the image of `P` is `⟨π(g)^k π(H) π(g)^{-k}⟩`. In an abelian quotient this is
  `π(H)`.

## Step 4: representations (N3)

A representation `ρ` extends to a ring map `ZG → M_n(k)`. Applied to `Σ c_x d_x = 1`, it gives
`Σ ρ(c_x) ρ(d_x) = I_n`. So the block row `(ρ(c_x))` has rank `n`.

For `n = 1`, `c^χ ≠ 0`. Twisting the cellular chain complex of the one-vertex model `K_B ≃ C` by
`χ|_H` gives `∂_χ e_j = Σ_x χ(∂_x u_j) x`. So

`∂_χ(e_1 - εχ(g) e_0) = -c^χ`,

and `c^χ = 0` exactly when `e_1 - εχ(g) e_0` is a twisted 2-cycle. ∎

## Calibration

- **ab = 0.** Say `a = 0` and `b = ±1`. Then `u = ∓1` is a unit and no condition on `g` arises. This
  matches the unit Fox coefficients of (U4) of `two-cell-core-deletions-need-a-unit-fox-coefficient`,
  where `ab = 0` cores can be admissible.
- **Torus.** `(a,b) = (1,-1)` with `ε = 1`. Then `A - b = 2 ≠ ±1`. Step 3 already fails at the
  augmentation, which matches the non-admissibility recorded in that node's calibration.
