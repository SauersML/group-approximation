---
rg: 2
id: kt-monomial-split-coset-wreaths-collapse-to-gamma
kind: claim
title: For the Theorem E pair a hyperlinear coset wreath over a monomial-split overgroup of Gamma, including every one-compressor ascending HNN, forces W_Gamma hyperlinear
distinct_from:
  kt-pair-hyperlinear-floor-below-normal-closure: that asks for some hyperlinear W_Δ with Γ ≤ Δ and ⟨⟨Γ⟩⟩ ⊄ Δ; this shows that the natural explicit candidates for Δ give nothing beyond Δ = Γ
  hyperlinear-wreath-model: that is the open case Δ = Γ; this reduces the monomial-split cases to it and does not decide it
  kt-intermediate-coset-wreaths-are-nonsofic: that proves nonsoficity for all intermediate Δ, HNN subgroups included; this compares hyperlinearity across those Δ
  kt-compressor-stable-overgroups-have-polynomial-content: that constrains the root subgroups of any compressor-stable overgroup; this computes the compressor core of a split family exactly
---

**ESTABLISHED (proposed; proof in `kt-monomial-split-coset-wreaths-collapse-proof`).**
Notation as in `kt-compressor-stable-overgroups-have-polynomial-content`
(`A ⊂ R`, `Γ = EL_r(A) < G = EL_r(R) ⋊ SL_d(Z)`, `r,d ≥ 3`, `Mon = SL_d(Z) ∩ M_d(N)`
acting on exponents).

1. **(Compressor core.)** For every `Δ ⊇ Γ`, `Δ' = ∩_(P∈Mon) P^(-1)ΔP` contains `Γ`, and
   `W_Δ` hyperlinear implies `W_(Δ')` hyperlinear.
2. **(Monomial-split overgroups.)** Let `M ⊆ Z^d` be a submonoid with `N^d ⊆ M ≠ Z^d`,
   let `Q ≤ Stab_(SL_d(Z))(M)`, and put `Δ_(M,Q) = E_r(F_q[M]) ⋊ Q`, which contains `Γ`.
   Then `Δ_(M,Q)' = Γ`. Hence

   ```text
   W_(Δ_(M,Q)) hyperlinear  ⟹  W_Γ hyperlinear  (hyperlinear-wreath-model).
   ```
3. **(HNN candidates.)** For `t ∈ Mon`, `⟨Γ,t⟩ = E_r(F_q[M_t]) ⋊ ⟨t⟩` with
   `M_t = ∪_n t^(-n)N^d`. Here `M_t` is proper, since it lies in the half-space
   `λ·v ≥ 0` for a Perron--Frobenius eigenvector `λ ≥ 0` of `t^T`. So part 2 applies:
   **a hyperlinear `W_⟨Γ,t⟩` makes `W_Γ` hyperlinear.** The same holds for half-space
   monoids `M = {λ·v ≥ 0}` with `λ ≥ 0`, with `Q` any subgroup of their stabilizer.
4. **(Finite permutation extensions.)** If `Γ ≤ Δ ≤ Γ ⋊ Perm_d` and `Δ` is `Mon`-stable,
   then `Δ = Γ`.

So the one-compressor ascending HNN subgroups and the monomial-split overgroups, the
explicit candidates named in `kt-pair-hyperlinear-floor-below-normal-closure`, bring no
discount over `hyperlinear-wreath-model`. For a hyperlinear wreath below the normal
closure, the only remaining candidates are non-split `Mon`-stable overgroups with
polynomial elementary content.

DERIVATION
kt-monomial-split-coset-wreaths-collapse-proof
