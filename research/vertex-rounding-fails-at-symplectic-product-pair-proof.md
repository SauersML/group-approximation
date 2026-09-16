---
rg: 2
id: vertex-rounding-fails-at-symplectic-product-pair-proof
kind: route
title: Multiply the Theorem E pair by the affine symplectic group, tensor Heisenberg models with residual permutation models, and run the Heisenberg-cover bimodule argument at amplified dimension
target: vertex-rounding-fails-at-symplectic-product-pair
requires:
  - kun-thom-nonsofic-wreath
  - rf-kazhdan-group-not-flexibly-hs-stable
  - bdhv-central-extension-property-t
artifacts:
  - research/artifacts/vertex-rounding-product-pair-2026-09-16.md
---

Notation as in the claim. Section numbers refer to the artifact, which proves each step in full.

1. **Readings of (H1) (§0).** Normalized padding and Dogon's compression both give genuine
   `π'_n : Γ -> U(D_n)`, `D_n/n -> 1`, with `||σ_n(s) ⊕ 1 - π'_n(s)||_(2,D_n) -> 0` on `F`. The compression
   error is controlled by the `(1,1)` block plus `6(D_n - n)/D_n`. Since `σ` is a homomorphism, the estimate
   propagates from a generating set to every element of `Γ`.
2. **Property (T) facts (§1).** Kazhdan sets generate, Kazhdan groups have finite abelianization, and
   `(Q_1 × e ∪ e × Q_2, min(κ_1, κ_2)/2)` is a Kazhdan pair for a product.
3. **The pair (§2).** (T) and residual finiteness pass to products. Conjugation acts coordinatewise, so
   `P_Γ = Γ_g × P_K`, which generates `Γ_g × H`. Non-normality comes from the second factor. Premises:
   `kun-thom-nonsofic-wreath` (Theorem E) and item 1 of `rf-kazhdan-group-not-flexibly-hs-stable`.
4. **The Heisenberg cover (§3).** `Γ~_g` is a central extension of `Γ_g` by `<z>`. Commutators give
   `2[z] = 0`. Transvections kill the image of `Z^(2g)` modulo `[z]`. `Sp_(2g)(Z)` is a quotient of `Γ_g`, so
   its abelianization is finite. Hence `Γ~_g^(ab)` is finite and `bdhv-central-extension-property-t` gives
   (T). Fix a Kazhdan pair `(Q~, κ~)`, a generating set `S_0` of `Γ_g`, and a word length `L` for `Q~`
   in `s(S_0)^(±1) ∪ {z^(±1)}`.
5. **Uniform amplified obstruction (§4).** Let `ρ` be a genuine representation of `Γ~_g` on `C^d` with
   `ρ(z) = ζ ≠ 1`. If `π : Γ_g -> U(D)` satisfies `(D - d)/d <= ε` and
   `||ρ(s(a)) - Pπ(a)P*||_(2,d) <= ε` on `S_0`, then `P` moves by at most `L·max(ε + √ε, |ζ - 1|)` under `Q~`
   in the bimodule `ξ -> ρ(x) ξ π(q(x))*`. That bimodule has no invariant vectors, so this bound is
   `>= κ~`. The constants do not depend on `d`.
6. **The model (§5).** `σ_(N_j) = α_(k_j) ⊗ λ_j`, with `N_j = d_(k_j) m_j` strictly increasing, and `σ_n = 1`
   off `D`. The multiplicative defect is at most `2π|c|/k_j`. The trace is `tr α_(k_j) · tr λ_j -> δ_e`,
   using item 2 of `rf-kazhdan-group-not-flexibly-hs-stable` and the residual chain of `H`. For a `U` fixed in
   advance, amplify `α_(k_j(n)) ⊗ λ_(j(n))` by `1_(t_n)` and pad by `r_n = o(n)` at every `n` (Remark 6.3).
7. **Failure (§6).** Given (H1), take `ρ = ρ~_(k_j) ⊗ 1_(m_j)` and `π(a) = π'_n(a, e)`. Step 1 gives errors
   `<= ε_0` on a `U`-large set, and `|e^(2πi/k_j) - 1| < κ~/L` for large `j`. Step 5 gives a contradiction.
