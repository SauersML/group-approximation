---
rg: 2
id: zp-restriction-trivial-splits-cellular-plus-phantom
kind: claim
title: A Z/p-algebra with contractible restriction splits, by the norm idempotent of its action element, into a trivial-action retract and an equivariant phantom
distinct_from:
  zp-algebras-with-contractible-restriction-are-cyclotomic: that makes the representation ring act through Z[zeta_p, 1/p]; this uses the second central element, the action automorphism, to split the object and characterize phantoms.
  zp-detection-equals-meyer-nadareishvili-sufficiency: that equates detection with a literature question; this gives a dynamical criterion, triviality of the action automorphism in KK^G, and a canonical splitting.
---

**ESTABLISHED (derivation; standard inputs named in the proof route).** Let
`p` be prime, `G = Z/p` with generator `ω`, and `KK^G` separable `G`-C\*-algebras.

1. **The action element.** For every `G`-algebra `(A, α)`, the automorphism
   `α_ω` is `G`-equivariant because `G` is abelian. Its class
   `θ_A := [α_ω] ∈ KK^G(A, A)` is a natural automorphism of the identity
   functor of `KK^G`:
   - `[α_ω] ⊗_A x = x ⊗_B [β_ω]` for all `x ∈ KK^G(A, B)`;
   - `θ^p = 1`, `θ_(A⊗B) = θ_A ⊗ θ_B`, and `θ = 1` on trivial actions.
2. **Crossed products.** `A ⋊ G ≃_KK 0` iff `1 − θ_A` is invertible in
   `KK^G(A, A)`. This is the Baaj–Skandalis dual of: `Res A ≃ 0` iff `1 − χ` is
   invertible, with `χ` a generating character.
3. **Splitting.** Let `Res E ≃_KK 0`. Then `p` is invertible and
   `e := (1 + θ_E + ⋯ + θ_E^(p−1))/p` is a central idempotent of `KK^G(E, E)`,
   so `E ≅ eE ⊕ (1 − e)E`.
   - `(1 − e)E` is an **equivariant phantom**: its restriction and crossed
     product are both KK-contractible.
   - `eE` has `θ = 1`, and is a retract of the trivial-action algebra
     `τ(E ⋊ G)`: `eE ≅ e_diag · τ(eE ⋊ G)` for an explicit idempotent `e_diag`,
     and `eE ⋊ G ≅ E ⋊ G`.
4. **Dynamical form of detection.** The following are equivalent:
   - `zp-restriction-and-crossed-product-detect-kk-g-contractibility`, for all
     separable algebras or for nuclear ones;
   - for every such `(E, α)` with `Res E ≃_KK 0`, the automorphism `α_ω` is
     trivial in `KK^G(E, E)`.
5. **Bootstrap membership on the contractible layer.** If `Res E ≃ 0`, then
   `E ∈ B^G` iff `θ_E = 1` and `E ⋊ G ∈ B`. Dually, if `F ⋊ G ≃ 0`, then
   `F ∈ B^G` iff `χ` acts as `1` on `F` and `Res F ∈ B`, and `F` is then a
   retract of the induced algebra `Ind Res F`.
6. **Tensor squares of phantoms.**
   - **`p = 2`.** Every phantom `D` has `χ = θ = −1`. Its tensor square has
     `θ = 1`, so `D ⊗ D` is a retract of `τ((D ⊗ D) ⋊ Z/2)`.
   - **Odd `p`.** `θ_D ⊗ 1` and `1 ⊗ θ_D` make `KK^G(D ⊗ D, D ⊗ D)` an algebra
     over `Z[ζ_p, 1/p]^⊗2 ≅ ∏_(σ ∈ Gal) Z[ζ_p, 1/p]`. The trivial-action part
     `e(D ⊗ D)` is the component `σ(ζ) = ζ^(−1)`. The other `p − 2` components
     are phantoms.

**What this says about a UCT counterexample shape.** By item 4, an equivariant
phantom is exactly a nuclear `Z/p`-action on a KK-contractible algebra whose
generator is **not KK^G-equal to the identity**. Realize it as a pointwise outer
action on `O_2 ⊗ K`. Meyer (arXiv:1906.11163, Theorem 2.1, as quoted in
arXiv:2406.11787v2 Theorem 5.11) gives an outer action on a stable Kirchberg
algebra, and `Res ≃ 0` forces that algebra to be `O_2 ⊗ K`. A candidate then
has to be an outer action whose
automorphisms `α_g` are not equivariantly asymptotically inner in the KK^G
sense, while `O_2 ⋊ Z/p` is still KK-contractible. This asymptotic reading of
`θ = 1` goes through Gabe–Szabó's uniqueness theorem and is not verified here.
Equivalently, a phantom is an object on which the central element
`u = (1 − χ)(1 − θ)` is invertible. Every `u`-telescope
`hocolim(A →u A →u ⋯)` is a phantom or zero.

Proof: `zp-restriction-trivial-splits-cellular-plus-phantom-proof`.
