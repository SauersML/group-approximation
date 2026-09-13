---
rg: 2
id: cantor-punctured-birman-section-orbit-proof
kind: route
title: A finite orbit gives a point stabilizer of finite index, and forgetting the rest of the set splits the Birman sequence over it
target: cantor-punctured-birman-sections-have-no-finite-end-orbit
requires:
  - birman-exact-sequence-does-not-virtually-split
  - birman-sequence-genus-three-does-not-virtually-split
artifacts:
  - research/artifacts/bh-mcg-closed-surface-2026-09-12.md
---

Let `Σ`, `E`, `L` and `σ` be as in the target, and suppose `x ∈ E` has a finite
`σ(L)`-orbit.

1. **Finite-index stabilizer.** `L_x = {ℓ ∈ L : σ(ℓ)·x = x}` has index in `L`
   equal to the orbit size. So `L_x` has finite index in `Mod(Σ)`.
2. **Forgetting `E ∖ {x}`.** Let `P = Stab_{Mod(Σ,E)}(x)`. Every representative
   of a class in `P` fixes `x`, since the action on `E` is well defined. An
   isotopy through homeomorphisms preserving `E` fixes `x` throughout. So
   `r: P → Mod(Σ, x)`, sending a class to the class of the same homeomorphism,
   is a well-defined homomorphism. Here `Mod(Σ, x)` allows only isotopies fixing
   `x`.
3. **A virtual section.** Let `p: Mod(Σ, x) → Mod(Σ)` forget `x`. Then
   `p∘r = F|_P`. With `s = r∘σ|_{L_x}` this gives `p∘s = F∘σ|_{L_x} = id_{L_x}`.
   So the Birman exact sequence `1 → π1(Σ, x) → Mod(Σ, x) → Mod(Σ) → 1` splits
   over the finite-index subgroup `L_x`.
4. **Contradiction.**
   - For `g ≥ 4`, this contradicts Theorem A of Chen--Salter,
     `birman-exact-sequence-does-not-virtually-split`.
   - For `g = 3`, it contradicts `birman-sequence-genus-three-does-not-virtually-split`.

Hence every orbit is infinite. Injectivity of `σ` was not used. `∎`
