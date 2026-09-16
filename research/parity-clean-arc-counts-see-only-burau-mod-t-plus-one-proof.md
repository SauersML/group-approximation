---
rg: 2
id: parity-clean-arc-counts-see-only-burau-mod-t-plus-one-proof
kind: route
title: "Loop classes in the cyclic cover, the Burau action at t = −1, and winding parity"
target: parity-clean-arc-counts-see-only-burau-mod-t-plus-one
requires: []
artifacts:
  - research/artifacts/zp-burau-parity-t-minus-one-obstruction-2026-09-16.md
---

Full proof: artifact §§1–7. Outline of the steps and where each is proved:

1. **Intersection form (§2).**
   - `D̃ → D_n` is the infinite cyclic cover for total winding, `P̃_*` is the fibre over `p_*`,
     and `H = H_1(D̃, P̃_*)`.
   - Collapsing the complement of the `ℓ`-th lift of a tubular neighbourhood of `α°` gives a map
     of pairs `f_ℓ : (D̃, P̃_*) → (S^1, pt)`.
   - `I = Σ_ℓ (f_ℓ)_* t^ℓ` is a `Z[t^{±1}]`-linear map `H → Z[t^{±1}]`. On a transverse path it
     counts signed crossings with the lifts `t^ℓ α̃`.
2. **Loop class (§3, Lemma 3.1).** Let `c_A` be the loop that runs along `A`, around the endpoint
   and back.
   - Its lift from the base point satisfies `I([c̃_A]) = (1 − t^s) 𝕄(α, A)`, with `s = ±1` fixed.
   - Hence `𝕄(α, A)` is a homotopy invariant (`Z[t^{±1}]` is a domain), and
     `I([c̃_A])(−1) = 2 𝕄(α, A)(−1)`.
3. **Burau action (§4).** A mapping class `h` lifts to `h̃` fixing `p̃_*`, commuting with deck
   transformations and preserving `P̃_*`.
   - `H` is free on the lifts `e_j` of a standard free basis `x_j`, and the Fox calculus gives
     `h̃_*(e_j) = Σ_k φ(∂h_*(x_j)/∂x_k) e_k`.
   - Artin's formula (Birman 1974, Ch. 1; Kassel–Turaev 2008, Ch. 1; locators not re-checked):
     `σ_i` acts on `π_1` by `A_i^{±1}`, where `A_i: x_i ↦ x_i x_{i+1} x_i^{-1}, x_{i+1} ↦ x_i`.
     Fox calculus then gives `J_{A_i} = ρ_n(σ_i)`.
   - So in some basis the matrix of `h̃_*` is `ρ_n(w')`, possibly with `t ↦ t^{-1}`, for `w'` one
     of `w`, `rev w`, `mirror w`, `rev mirror w`.
   - `ρ_n(w)^T = D ρ_n(rev w) D^{-1}` with `D = diag(1, t, ..., t^{n−1})`, and
     `ρ_n(mirror w) = D^{-1} (ρ_n(w)^{-1})^T D`.
   - Hence `ρ_n(Ψ) ≡ I mod (t+1)` gives `h̃_{Ψ,*} ≡ id mod (t+1)H` in every convention
     (Lemma 4.1).
4. **Theorem A (§5).** Let `A = (β_*^3)ΨΓ` and `B = (β_*^3)Γ`.
   - `[c̃_{k(β)}] = k̃_*[c̃_β]` for every mapping class `k`.
   - So `[c̃_A] − [c̃_B]` lies in `(t+1)H` for either composition order. For `ΨΓ = g ∘ h`,
     linearity of `g̃_*` carries `(h̃_* − 1)[c̃_β] ∈ (t+1)H` into `(t+1)H`.
   - Applying `I` and item 2: `2𝕄(α, A)(−1) = 2𝕄(α, B)(−1)` (Corollary A2).
5. **Winding identity (§6, Lemma 6.1; Bigelow 1999, §3).** If `A` crosses `t^{k_i} α̃` over
   `q_i`, then `k_{i+1} − k_i = ±|P ∩ Δ_i|`.
   - Lift the simple closed curve `∂Δ_i`: its total winding is `k_{i+1} − k_i`.
6. **Parity lemma (§6, Lemma 6.2).** By item 5, `(−1)^{k_{i+1} − k_i} = (−1)^{|P ∩ Δ_i|}`.
   - So the parity condition is equivalent to `ε_i (−1)^{k_i}` being constant in `i`.
   - `𝕄(α, A)(−1) = Σ_i ε_i (−1)^{k_i}` is a sum of `m = |A ∩ α|` signs, whose absolute value is
     `m` iff all the signs agree.
   - This proves part 1 of the claim.
7. **Conclusion (§7, Theorem B).** For parity-clean representatives `A'`, `B'`:
   `|A' ∩ α| = |𝕄(α, A)(−1)| = |𝕄(α, B)(−1)| = |B' ∩ α|`. ∎

Imported inputs:
- Artin's formula for the half-twist action on `π_1(D_n, p_*)`, classical, with locators not
  re-checked.
- Bigelow's winding remark, which is reproved in item 5.
- The definition of the parity condition, from arXiv:2607.05283v1, Lemma 4.2, as recorded in
  `zp-burau-n4-verification-2026-09-13-part1.md` (S4–S5).

For the braid `Φ_0` used in `parity-correcting-push-fails-via-minus-one-kernel`, the needed
congruence `h̃_* ≡ id mod (t+1)` was also checked directly. The Fox Jacobians at `t = −1` of both
automorphism conventions, in both composition orders, equal `I` (script check 6).
