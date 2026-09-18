---
rg: 2
id: loop-braid-distortion-from-free-factor-systems-proof
kind: route
title: The extended symmetric automorphisms are the full preimage in Aut(F_n) of the stabilizer of the coindex n-1 free factor system of basis letters
target: loop-braid-groups-are-distorted-in-aut-free-groups
requires:
  - free-factor-system-stabilizers-distortion-dichotomy
  - aut-free-groups-quasi-isometrically-embed-in-fp-simple-groups
---

1. **The free factor system.** Let `F = {[⟨x_1⟩], …, [⟨x_n⟩]}`. Since `F_n = ⟨x_1⟩ * ⋯ * ⟨x_n⟩`, it is a
   free factor system. Its coindex is `(n−1) − Σ_i (1−1) = n−1`, which is `>= 2` for `n >= 3`. So
   `Stab(F)` is distorted in `Out(F_n)` (`free-factor-system-stabilizers-distortion-dichotomy`, Theorem 8(2)).
   `Stab(F)` is defined there as a set stabilizer, so it may permute the components.
2. **Its preimage is Σ^±_n.** `φ ∈ Aut(F_n)` maps into `Stab(F)` exactly when each `⟨x_i⟩` goes to a conjugate
   of some `⟨x_{π(i)}⟩` with `π` a permutation, i.e. when `φ(x_i) = w_i x_{π(i)}^{±1} w_i^{-1}`. So the full
   preimage of `Stab(F)` is `Σ^±_n`. In particular `Inn(F_n) ≤ Σ^±_n`, and `q: Σ^±_n → Stab(F)` is surjective.
3. **Transfer to Aut.** Fix generators of `Aut(F_n)` and give `Out(F_n)` their images, so that every element
   of `Out`-length `ℓ` has a lift of `Aut`-length `ℓ`. By step 1 there are `ψ_k ∈ Stab(F)` with
   `|ψ_k|_{Stab(F)} / |ψ_k|_{Out} → ∞`.
   - Lift `ψ_k` to `ψ̂_k ∈ Aut(F_n)` with `|ψ̂_k|_{Aut} = |ψ_k|_{Out}`. By step 2, `ψ̂_k ∈ Σ^±_n`.
   - `q` is a homomorphism of finitely generated groups, so it is `L`-Lipschitz, and
     `|ψ̂_k|_{Σ^±_n} >= |ψ_k|_{Stab(F)} / L`.
   - So `|ψ̂_k|_{Σ^±_n} / |ψ̂_k|_{Aut} → ∞`, and `Σ^±_n` is distorted in `Aut(F_n)`.
4. **Finite index.** Recording the signs and `π` gives a homomorphism `Σ^±_n → (Z/2)^n ⋊ S_n`. Its kernel is
   `PΣ_n`, and `Σ_n` lies between the two groups. So both have finite index in `Σ^±_n`. A finite-index
   inclusion is a quasi-isometry, so they are distorted as well.
5. **The host.** By part 2 of `aut-free-groups-quasi-isometrically-embed-in-fp-simple-groups`, a finitely generated
   subgroup of `Aut(F_n)` has the same distortion in `SV_Γ` as in `Aut(F_n)`. ∎
