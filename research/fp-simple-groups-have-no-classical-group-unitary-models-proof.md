---
rg: 2
id: fp-simple-groups-have-no-classical-group-unitary-models-proof
kind: route
title: Perfectness moves the generators into the commutator subgroups, which Larsen–Shalev–Tiep make gapped
target: fp-simple-groups-have-no-classical-group-unitary-models
requires: [fp-simple-groups-have-no-gapped-finite-unitary-models, lst-quasisimple-classical-character-ratio-bound]
artifacts: [research/artifacts/sk-fp-sofic-c-unitary-gap-2026-09-13.md]
---

Suppose `φ_k : X → Q_k` and `ρ_k` give an injective homomorphism `Π : S → ∏_ω U(d_k)` extending `x ↦ (ρ_k(φ_k(x)))_ω`.
For a word `w` in `X`, write `W_k(w)` for the product of the `φ_k(x)^{±1}` along `w`. Then `Π(w̄) = (ρ_k(W_k(w)))_ω`, because `ρ_k`
is a homomorphism.

1. **Commutator generators.**
   - `S` is infinite and simple, hence perfect.
   - Each `x ∈ X` equals, in `S`, a product of commutators `[a,b]` of words `a, b` in `X`.
   - Let `X'` be the finite set of the commutators used. It generates `S`, and `S` is finitely presented on `X'`, since finite
     presentability does not depend on the finite generating set.
2. **The new maps land in the commutator subgroups.** For `x' = [a,b] ∈ X'`, put `φ'_k(x') = W_k(a)W_k(b)W_k(a)^{-1}W_k(b)^{-1}`.
   - This lies in `[Q_k,Q_k]`.
   - `Π(x') = (ρ_k(φ'_k(x')))_ω`.
   - So `x' ↦ (ρ'_k(φ'_k(x')))_ω`, with `ρ'_k = ρ_k|_{[Q_k,Q_k]}`, extends to the same injective homomorphism `Π`.
3. **Gap.** By `lst-quasisimple-classical-character-ratio-bound`, the family `[Q_k,Q_k]` is θ-gapped with `θ = 2^{-1/481}`.
4. **Conclusion.** `fp-simple-groups-have-no-gapped-finite-unitary-models` gives the contradiction.
   - Its proof uses the maps only through the products `W_k` on generators (its Step 0).
   - So maps defined on `X'` suffice: extend them to `S` along fixed words.

**Sofic special case.** An action of `Q_k` on a finite set gives the permutation representation, and normalized fixed-point
counts are normalized traces. So a sofic approximation through such actions is a hyperlinear approximation of the excluded
kind.
