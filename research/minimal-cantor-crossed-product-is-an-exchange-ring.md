---
rg: 2
id: minimal-cantor-crossed-product-is-an-exchange-ring
kind: claim
title: The algebraic crossed product LC(X,k) ⋊ Z of a minimal Cantor system is an exchange ring
distinct_from:
  minimal-cantor-crossed-product-has-stable-rank-at-most-two: that asks for Bass stable range, which feeds Vaserstein's theorem; this asks for Nicholson's exchange property, which feeds Preusser's theorem with no stable range.
artifacts:
  - research/artifacts/sk-stable-rank-a-shortcut-2026-09-13-part1.md
---

**OPEN.** Let `k` be a field, `(X,T)` a minimal homeomorphism of the Cantor set, and `R = LC(X,k) ⋊_T Z`. Is `R`
an exchange ring, i.e. for every `a ∈ R` is there an idempotent `e ∈ aR` with `1 − e ∈ (1−a)R`?

If yes, `standard-normal-structure-makes-simple-ring-el-simple` and Preusser's Theorem 3
(`preusser-exchange-rings-have-standard-normal-subgroups`) give simplicity of `EL_n(R)/Z` for every `n ≥ 3` in a few
lines. This is the algebraic analogue of real rank zero for `C(X) ⋊ Z`. Simplicity itself no longer depends on it
(`amenable-crossed-products-meet-stepanov-condition-b`), so the question stays open as ring theory.

## Attempts

- **A Laurent test case works (verified).** Over `F_2`, `a = u + u^2` is not suitable in `F_2[u^{±1}]`, but it is
  suitable in `R`. The witness is `e = 1 + pΦ` with `p = 1 + u + u^2` and `Φ` the tower-to-base map of a
  Kakutani–Rokhlin partition with heights ≥ 3. Then `ΦpΦ = Φ`, `1 − e ∈ pR` and `e = (1+u)(ρ_0 + uΦ) ∈ aR`
  (artifact §2.2). The same mechanism is expected for every Laurent polynomial, but this is not written.
- **Necessary condition holds (verified).** Every nonzero one-sided ideal contains a nonzero idempotent, through
  local annihilation (artifact §2.3).
- **Morita bootstrapping (circular).** Exchange is Morita invariant, and corners by clopen idempotents are crossed
  products of induced systems of the same type.
- **General elements (stuck).** By Nicholson's criterion one needs an idempotent in `a + (a − a^2)R` for every `a`.
  For `a` with locally constant coefficients interacting across the cuts, no tower construction of `e` was found.
- **Model tests.** `k[u^{±1}]` fails the property. It is the Z-crossed product of a one-point space, where T has a
  fixed point. The locally matricial `A_Y` has the property.
- **Laurent elements are suitable (established, unreviewed; sk-algebraic-putnam 2026-09-13).** Every `p ∈ F[u^{±1}]` is suitable, and the idempotent lies in a tower algebra. It is the projection onto the preimage of `0 × F[u]/(r_0)` along the kernel plus the preimage of the first factor, on each block of the Chinese-remainder residue map `F^h → F[u]/(p_0) × F[u]/(r_0)`, where `p = u^αp_0` and `1−p = u^βr_0`. See `laurent-elements-of-cantor-crossed-products-are-suitable`, which generalizes the `u+u²` witness above. The method needs `laurent-right-ideals-of-cantor-crossed-products-columnwise`, that is, right ideals characterized columnwise. That fails for general `a` (e.g. `e_WR`), where the exchange property stays open.
