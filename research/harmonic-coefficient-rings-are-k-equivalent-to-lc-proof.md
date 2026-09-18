---
rg: 2
id: harmonic-coefficient-rings-are-k-equivalent-to-lc-proof
kind: route
title: Excise the germs along the singular fibres and use homotopy invariance of LC(S,Q)[t]
target: harmonic-coefficient-rings-are-k-equivalent-to-lc
requires:
  - harmonic-elimination-puts-q-in-odometer-crossed-products
---

**Imports.**
- (E) Suslin's excision theorem, quoted from Tamme, arXiv:1703.03331, Theorem 1 (read on ar5iv): "If I is
  Tor-unital, then I satisfies excision in algebraic K-theory."
  - Tor-unital means `Tor^(Z⋉I)_i(Z,Z) = 0` for `i > 0`, and "every unital ring is Tor-unital".
  - Excision is taken in the sense recalled in Tamme's introduction: for `A -> B` mapping the ideal `I`
    isomorphically onto an ideal of `B`, the square formed by `K(A)`, `K(A/I)`, `K(B)`, `K(B/I)` is
    homotopy cartesian. That formulation was not quoted verbatim.
- (H) `K(A) ≃ K(A[t])` for regular noetherian `A` (Quillen), as cited in the reviewed route
  `elementary-groups-over-polynomial-s-integers-are-fp-proof`.
- (C) `K`-theory, and `Tor`, commute with filtered colimits of rings.

**Part 1.** `F` is `Γ`-invariant (`(f∘γ)∘g^(-1)` is again a translate), so `F ⋊_alg Γ` is a ring.
- It contains the generators of `R`, so `R ⊆ F ⋊ Γ`.
- Conversely `R` contains `LC(X,Q)`, the `u_γ` and `f`, hence `f ∘ γ = u_γ^(-1) f u_γ`, hence `F` and
  `F ⋊ Γ`.
- The degree-`e` part of `F ⋊ Γ` is `F`.

For `R_T`, part 1 of its node gives `LC(X,Z) ⊆ R_T` and `Q ⊆ R_T`, so `LC(X,Q) ⊆ R_T`.

**Singular fibres.** Put `h_γ = f∘γ`, so `h_γ(x) = f_K(γ π x)`. The action on `K` is free: `γy = y`
forces `γ ∈ ∩_n Γ_n = 1`. So the fibres `S_γ` are pairwise disjoint.
- `h_γ` is locally constant on `X ∖ S_γ`, with values `1/(1+ℓ)`, and `h_γ = 0` on `S_γ`.
- Fix `Φ` and pairwise disjoint clopen sets `W_γ ⊇ S_γ` (`γ ∈ Φ`). On `W_γ` the `h_γ'` with `γ' ≠ γ`
  are locally constant, so every `g ∈ F_Φ` satisfies `g|W_γ = Σ_k φ_k h_γ^k` with `φ_k ∈ LC(W_γ, Q)`.

**Germs are well defined.** Suppose `Σ_k φ_k h_γ^k = 0` on `W_γ` and `x ∈ S_γ`.
- Let `V ∋ x` be clopen with every `φ_k` equal to a constant `c_k` on `V`.
- `S_γ` has empty interior, so `V` contains points `x_j -> x` off `S_γ`. Their levels `ℓ(γπx_j)` are
  finite and tend to `∞`, so they take infinitely many values.
- So `Σ c_k s^k` vanishes at infinitely many `s = 1/(1+ℓ)`. Hence every `c_k = 0` and `φ_k|S_γ = 0`.

Thus `G_γ(g) = Σ_k (φ_k|S_γ) t^k` is a well-defined ring homomorphism `F_Φ -> LC(S_γ,Q)[t]`.

**The pullback (part 3).** Let `G = (G_γ)_γ : F_Φ -> P = ⊕_Φ LC(S_γ,Q)[t]`.
- *Onto.* Extend LC functions from `S_γ` to `W_γ`, and multiply by powers of `h_γ`.
- *Kernel.* If every germ vanishes, the `φ_k` vanish on a clopen `W'_γ ⊇ S_γ`, so `g = 0` there. Off
  `∪ W'_γ` every `h` is locally constant. So `ker G = I`, the locally constant functions vanishing near
  `Σ_Φ = ∪_Φ S_γ`.
- Restriction `ρ : LC(X,Q) -> P_0 = ⊕_Φ LC(S_γ,Q)` is onto with the same kernel `I`.
- `I` is an ideal of both rings: an element of `F_Φ` is locally constant on the support of any `g ∈ I`.
- The inclusion induces the identity on `I` and the constant-polynomial map `P_0 -> P` on quotients.

**Part 2.** `I` is the filtered union of the unital rings `LC(V,Q)`, for clopen `V` disjoint from a
neighbourhood of `Σ_Φ`. So it is Tor-unital by (C) and (E).
- By (E), the square formed by `K(LC(X,Q)) -> K(P_0)` and `K(F_Φ) -> K(P)` is homotopy cartesian.
- `LC(S_γ, Q)` is the filtered colimit of the finite products `Q^m`, and `LC(S_γ,Q)[t]` is the colimit
  of `Q[t]^m`. So `K(P_0) -> K(P)` is an equivalence by (H) and (C).
- The parallel map `K(LC(X,Q)) -> K(F_Φ)` is therefore an equivalence.

Finally `F = ∪_Φ F_Φ` is a filtered union, so `K(LC(X,Q)) ≃ K(F)` by (C). The map is the inclusion,
hence `Γ`-equivariant. The values `K_n(LC(X,Q)) = LC(X,Z) ⊗ K_n(Q)` for `n <= 2` follow as in Step 1 of
`cantor-crossed-clopen-symbols-factor-through-coinvariants-proof`. The idempotents of `F` are continuous
`{0,1}`-valued functions, so they are the clopen indicators. ∎
