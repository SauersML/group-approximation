---
rg: 2
id: thompson-f-sofic-iff-defect-to-separation-ratio-vanishes-proof
kind: route
title: Coordinatewise powers multiply fixed-point proportions, so a small defect-to-separation ratio amplifies to a separating almost-solution
target: thompson-f-sofic-iff-defect-to-separation-ratio-vanishes
requires:
  - thompson-f-sofic-iff-relator-system-unstable
---

Numbering follows the claim. `d` is bi-invariant, and `d(AB, BA) = d(A^-1B^-1AB, 1)`, because
`ABx ≠ BAx` exactly when `(BA)^-1AB` moves `x`.

**0. Powers.** Let `A^(×m)` act on `[n]^m` coordinatewise. For every word `w`,
`w(A^(×m), B^(×m)) = w(A,B)^(×m)`, whose fixed points are `Fix(w(A,B))^m`. So

`d(w(A^(×m), B^(×m)), 1) = 1 - (1 - d(w(A,B), 1))^m`.

With `w = a^-1 b^-1 a b` this gives separation `1 - (1-t)^m`, and with `w = R_j` the relator defects
`1 - (1-d_j)^m`.

**Item 3.**
- **Defect.** By Bernoulli's inequality `(1-x)^m ≥ 1 - mx`, each relator defect of the power is at most
  `m d_j ≤ mD`. With `m ≤ K/t + 1` and `D = ρt`, `mD ≤ Kρ + ρt ≤ (K+1)ρ`, since `t ≤ 1`.
- **Separation.** `1 - t ≤ e^-t` gives `1 - (1-t)^m ≥ 1 - e^(-mt) ≥ 1 - e^-K`, since `mt ≥ K`.

**Item 1.**
- **Sofic gives `ρ_F = 0`.** By `thompson-f-sofic-iff-relator-system-unstable`, item 3 fails. So there
  are `ε > 0` and pairs `(A_k, B_k)` with `D(A_k,B_k) < δ_k → 0` and `t(A_k,B_k) ≥ ε`. Then
  `D/t < δ_k/ε → 0`.
- **`ρ_F = 0` gives soficity.** Take `K = ln 2`. For `η > 0` choose a pair with `t > 0` and
  `D/t ≤ η/(K+1)`, and apply item 3. The power is an `η`-solution with separation at least `1/2`.
  As `η` is arbitrary, item 3 of `thompson-f-sofic-iff-relator-system-unstable` fails for
  `ε = 1/2`, so `F` is sofic by its equivalence `1 ⇔ 3`.

**Item 2.** If `ρ_F > 0`, then `t ≤ D/ρ_F` whenever `t > 0`, and trivially when `t = 0`. Conversely
a constant `C` gives `ρ_F ≥ 1/C > 0`. So item 2 is item 1 restated, and `D ≤ D_+ ≤ 2D` transfers it
to `D_+`.

**Item 4.**
- **Unions.** On a disjoint union, `t` and `D_+` are the averages of the two pairs' values weighted by
  size. So `D_+ ≥ r·t` passes to the union.
- **Products.** Let the two pairs have separations `s, s'` and relator defects `x_j` and `y_j`
  (`j = 1, 2`), with `x_1 + x_2 ≥ rs` and `y_1 + y_2 ≥ rs'`. By step 0 the product has separation
  `s + s' - ss'` and `D_+ = Σ_j (x_j + y_j - x_j y_j)`.
  - This expression is nondecreasing in each variable on `[0,1]`, since `∂/∂x_j = 1 - y_j ≥ 0` and
    symmetrically. So it is smallest on the feasible set when `x_1 + x_2 = rs` and `y_1 + y_2 = rs'`
    (both at most 1).
  - There it equals `rs + rs' - f`, with `f = x_1 y_1 + (rs - x_1)(rs' - y_1)`. The function `f` is
    affine in each of `x_1 ∈ [0, rs]` and `y_1 ∈ [0, rs']`, so its maximum is at a corner of that box.
    The corners give `r²ss'` or `0`.
  - Hence `D_+ ≥ r(s + s') - r²ss' ≥ r(s + s' - ss')` because `r ≤ 1`.
- **Torus factors.** A commuting pair has separation 0 and zero defects, so the product with it changes
  nothing.

**Item 5.**
- **Lower bound.** Every pair with `t ≥ τ` has `D ≥ ρ_F t ≥ ρ_F τ`, by the definition of `ρ_F`.
- **Upper bound.** Let `K = ln(1/(1-τ))`, so `1 - e^-K = τ`. For `ε' > 0` take a pair with `t > 0` and
  `D/t ≤ ρ_F + ε'`. Item 3 turns it into a pair with separation at least `τ` and defect at most
  `(K+1)(ρ_F + ε')`. Let `ε' → 0`. ∎
