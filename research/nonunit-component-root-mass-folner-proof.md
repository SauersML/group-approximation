---
rg: 2
id: nonunit-component-root-mass-folner-proof
kind: route
title: The compressor acts on unit and non-unit components separately and divides non-unit depth by d
target: nonunit-component-root-mass-is-log-scale-folner
requires:
  - compressor-transport-exactifies-under-vertex-rounding
  - unit-type-vertex-rounding-forces-compressor-commutant-rigidity
  - nonunit-projection-bounded-by-root-spectral-mass
---

Derivation, following `pure-nonunit-root-mass-folner-proof` with the whole-character depth replaced
by the depth of the non-unit component.

- **Components are well defined.**
  - Let `I ⊆ I'` be finite-index ideals inside `ker χ`. The local factors of `R_+/I'` are quotients of some local
    factors of `R_+/I`, with the same maximal ideals.
  - The type of a factor is a property of its maximal ideal: the factor is unit-type iff no `x_i` lies in that ideal.
  - So the unit idempotent of `R_+/I` maps to the unit idempotent of `R_+/I'`, and `χ_u`, `χ_nu` are the same for
    both choices.
- **Depth is finite.** If some `x_j` lies in a maximal ideal `m`, then so does `z`. The maximal ideal of a finite
  local ring is nilpotent, so `z` is nilpotent on `A_nu`. Hence `χ_nu` is trivial on `z^k R_+` once
  `z^k A_nu = 0`.
- **φ_A preserves types.**
  - Let `χ` kill `I_n`. Then `D_A χ` kills `I' = φ_A^(-1)(I_n)`, and `φ_A` induces an injective ring map
    `ι : R_+/I' -> B_n`.
  - For a maximal ideal `m ⊇ I_n`, put `m' = φ_A^(-1)(m)`.
  - We have `φ_A(x_i) = ∏_j x_j^(A_ji)` with every `A_ji >= 1`, and `m` is prime. So `φ_A(x_i) ∈ m` iff some `x_j ∈ m`,
    and `m'` is non-unit type iff `m` is.
  - The image of `R_+/I'` in the local factor `B_m` is local. So `ι` kills every idempotent except the one for
    `m'`, and it sends the unit idempotent `e'_u` to `Σ_(m unit-type) e_m = e_u`.
- **Item 1.**
  - `(D_A χ)_u(f) = χ(φ_A(e'_u f)) = χ(e_u φ_A(f)) = χ_u(φ_A f)`, and likewise for the non-unit component.
  - The image of `S = φ_A(R_+)` in `A_u` is all of `A_u`. The `x_i` are units there, `A ∈ SL_d(Z)`, and inverses of
    units in a finite ring are powers (item 2 of
    `unit-type-vertex-rounding-forces-compressor-commutant-rigidity`).
  - So `χ_u ∘ φ_A ≠ 1` iff `χ_u ≠ 1`.
- **Item 2.** `φ_A(z) = x^(A·1)` has every exponent `>= d`, so `φ_A(z^k R_+) ⊆ z^(dk) R_+`. If `χ_nu` is trivial on
  `z^(dk) R_+`, then `χ_nu ∘ φ_A` is trivial on `z^k R_+`.
- **Item 3.**
  - Put `F_j = μ_n(depth_nu <= d^j)`.
  - By item 2, `D_A^(-1){depth_nu <= d^j} ⊇ {depth_nu <= d^(j+1)}`.
  - Characters with finite-index conductor form a countable set, so every set here is Borel.
  - The total-variation bound of `compressor-transport-exactifies-under-vertex-rounding` gives
    `F_(j+1) <= μ_n(D_A^(-1){depth_nu <= d^j}) <= F_j + η_n`.
- **Item 4.**
  - As in `pure-nonunit-root-mass-folner-proof` item 4, `dim_(F_p) A_nu <= r(r-1)n'`.
  - `z^k A_nu` strictly decreases until it is `0`, so `depth_nu <= r(r-1)n'`.
  - Sum item 3 over the at most `1 + log_d(r(r-1)n')` d-adic blocks above depth one.
- **Item 5.**
  - `nonunit-projection-bounded-by-root-spectral-mass` gives `τ(1 - P_n) <= r(r-1)·μ_n(χ_nu ≠ 1)`, where
    `χ_nu ≠ 1` means nontrivial on the non-unit factor.
  - `{χ_nu ≠ 1} = {depth_nu = 1} ⊔ {depth_nu > 1}`. Apply item 4.
- **Tensor structure** (reading only).
  - `St_r(A_u × A_nu) = St_r(A_u) × St_r(A_nu)`, as used in `nonunit-projection-root-mass-proof`.
  - Irreducible representations of a product of finite groups are tensor products of irreducibles of the
    factors.
