---
rg: 2
id: symplectic-gaussian-actions-split-area-cocycles
kind: claim
title: "An affine action by restricted symplectic maps whose area cocycle represents a nonzero multiple of an extension class makes the extension split measurably over the nonsingular Gaussian space; if the linear Gaussian Koopman representation has almost invariant vectors, the extension is Haagerup whenever the quotient is"
distinct_from:
  central-extension-haagerup-from-measurable-euler-splitting: that turns a measurable splitting over an almost invariant space into the Haagerup property; this produces the splitting and the space from symplectic data, and feeds that claim
  central-zero-poincare-exponent-gives-euler-splitting: that uses the orthogonal affine action of a cnd function on the extension G and a dissipativity argument along the centre; this uses a symplectic, possibly non-orthogonal, affine action of the quotient Q and no dissipativity, the splitting being an explicit Gaussian linear functional
  lifted-thompson-t-euler-class-in-kahler-subspace: that asks for a unitary (Kähler) representation; here the linear part may be any restricted symplectic map, and the unitary case is the special case in which the Gaussian linear part preserves the measure
artifacts: []
---

**ESTABLISHED** by `symplectic-gaussian-actions-split-area-cocycles-proof`.

**Setting.**
- `Q` is a countable group and `1 → Z → E → Q → 1` a central extension, `z` the generator of the
  kernel, `σ : Q → E` a normalized section, `σ(g)σ(h) = z^{ε(g,h)} σ(gh)`.
- `(H, ω)` is a real separable symplectic Hilbert space with a complex structure `J`
  (`J² = −1`, `ω(Jx, Jy) = ω(x, y)`) such that `⟨x, y⟩ = ω(x, Jy)` is the inner product.
- `ρ : Q → Sp(H, ω)` is a homomorphism into bounded symplectic maps with `[ρ(g), J]`
  Hilbert–Schmidt for every `g` (the restricted symplectic group `Sp_res`).
- `c : Q → H` is a 1-cocycle, `c(gh) = c(g) + ρ(g)c(h)`, with area cocycle
  `Ω(g, h) = ω(c(g), ρ(g)c(h))`.
- Assume `Ω = a·ε + dβ₀` for some real `a ≠ 0` and function `β₀ : Q → R`, where
  `dβ₀(g, h) = β₀(g) + β₀(h) − β₀(gh)`. That is, `[Ω] = a·[ε]` in `H²(Q; R)`.

**Theorem.**
1. *(Gaussian space.)* Let `γ` be the standard Gaussian measure of `(H, ⟨,⟩)` on its canonical
   sequence-space model `X`. For each `t ∈ R` the affine maps `x ↦ ρ(g)x + t c(g)` extend to a
   nonsingular action `A^t` of `Q` on a conull subset `X_t ⊆ X`.
2. *(Splitting.)* For `t ≠ 0` there is a measurable `β_t : E × X_t → R`, with `E` acting through
   `Q`, satisfying the cocycle identity everywhere and `β_t(z, ·) = 1`. Explicitly,
   `β_t(σ(g)z^k, x) = (t^{-1} ℓ_{w(g)}(x) − β₀(g))/a + k`, where `w(g) = ρ(g)^* J c(g)` and `ℓ_w`
   is the Paley–Wiener (measurable linear) functional of `w`.
3. *(Almost invariance.)* Suppose the Koopman representation `κ₀` of the linear action `A^0` on
   `L²(X, γ)` has almost invariant unit vectors. Then the disjoint union of suitable `X_{t_n}`,
   `t_n → 0`, is a nonsingular `Q`-space with almost invariant Koopman vectors over which `E`
   splits measurably. So if `Q` is Haagerup, `E` is Haagerup, by
   `central-extension-haagerup-from-measurable-euler-splitting`.

**The unitary case.** If every `ρ(g)` commutes with `J`, then `A^0` preserves `γ`, the constant
function `1` is `κ₀`-invariant and part 3 applies unconditionally. So a unitary affine action with
area class `a·[ε]`, `a ≠ 0`, gives the Haagerup property of `E` for Haagerup `Q`. This is the
mechanism of the Kähler route, now for non-unitary linear parts.
