---
rg: 2
id: kazhdan-group-algebra-tate-part-has-no-phantom
kind: claim
title: For torsion-free Kazhdan hyperbolic Γ, the Tate part 1_T ⊗ C*_r(Γ^p) of the norm of C*_r(Γ) has zero equivariant phantom part
distinct_from:
  tate-norm-shift-is-kkg-trivial: that asks for every separable algebra A; this is the single case A = C*_r(Γ) for Kazhdan hyperbolic Γ, the adversarial non-nuclear test.
  kazhdan-tate-crossed-product-inclusion-is-kk-equivalence: that is the non-equivariant crossed-product half of the Tate diagonal question; this is the phantom half.
---

**OPEN.**
- **Setting.** `p` is prime, `G = Z/p`, and `Γ` is a torsion-free infinite hyperbolic group with
  property (T). `N(C*_r Γ) = C*_r(Γ^p)` carries the permutation action.
- **Question.** Is `(1 − e)(1_T ⊗ N(C*_r Γ)) ≃ 0`, where
  `e = (1 + θ + ⋯ + θ^(p−1))/p` is the norm idempotent of
  `zp-restriction-trivial-splits-cellular-plus-phantom`? Equivalently, is the shift `KK^G`-trivial on
  `1_T ⊗ C*_r(Γ^p)`?
- **Relations.**
  - This is `tate-norm-shift-is-kkg-trivial` at `A = C*_r Γ`.
  - Together with `kazhdan-tate-crossed-product-inclusion-is-kk-equivalence` it is equivalent to
    `kazhdan-group-algebra-tate-diagonal-is-kkg-equivalence`, by the split in
    `research/artifacts/uct-tate-diagonal-wreath-cone-2026-09-13-part2.md` §6.
- **Why it matters.** A nonzero phantom part refutes `MN(all separable)` at `Z/p`, by
  `zp-detection-equals-meyer-nadareishvili-sufficiency`.

## Attempts

- **Phantom transfer (reduction proved, part 3 of the norm-functor artifact).** The phantom part
  equals that of the cone `Z_Γ` of the Tate diagonal. `Z_Γ` is `Γ^p ⋉_r Y` for the wreath object
  `Y`, which vanishes on all visible subgroups.
- **Norm sum formula (conditional).** If `N` were additive modulo transfers on `KK(C*_r Γ, C*_r Γ)`,
  the phantom part would live on the Skandalis summand `N(f)`, with `f = 1 − j_r(γ)`, alone. The sum
  formula is not proved.
- **Self-tensoring (partial).** `θ` is monoidal, so `Γ × Γ'` moves the question to products and does
  not decide it.
- **Square-zero constraint at `p = 2` (derived, unreviewed; lane ex3-uct-tate-diagonal).**
  - Suppose `kazhdan-tate-crossed-product-inclusion-is-kk-equivalence` holds for `Γ` and for `Γ × Γ`.
    Under (P1) for `Γ`, `T(C*_r Γ) ≅ (1_T ⊗ τ C*_r Γ) ⊕ Φ`, where `Φ` is the phantom part and
    `T(Δ)` is an isomorphism onto the first summand.
  - `T(Δ_(Γ×Γ)) = T(Δ) ⊗ T(Δ)`, so its cone is `S ⊗ Φ ⊕ Φ ⊗ S ⊕ Φ ⊗ Φ`, with `S = 1_T ⊗ τ C*_r Γ`.
  - `θ = −1` on the two cross terms and `θ = +1` on `Φ ⊗ Φ`. So the non-phantom part of that cone is
    `Φ ⊗ Φ`, and (P1) for `Γ × Γ` forces `Φ ⊗ Φ ≃ 0` in `KK^(Z/2)`.
  - So a counterexample of the kind "(P1) true, this claim false" must be a **square-zero** equivariant
    phantom, realizable as an outer non-Rokhlin `Z/2`-action `α` on `O_2` with `α ⊗ α` Rokhlin.
  - Inputs: multiplicativity of `1_T ⊗ −` (`1_T ⊗ 1_T ≅ 1_T`) and item 6 of
    `zp-restriction-trivial-splits-cellular-plus-phantom`.
  - `Γ × Γ` satisfies Baum–Connes with coefficients with finite wreath products
    (Nishikawa–Petrosyan Thm. 4.3(5)).
