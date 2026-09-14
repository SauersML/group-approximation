---
rg: 2
id: fp-simple-groups-have-no-models-through-classical-products-proof
kind: route
title: A perfect group's model can be pushed into bounded-depth derived subgroups, where every constituent is gapped
target: fp-simple-groups-have-no-models-through-classical-products
requires: [fp-simple-models-concentrate-on-template-constituents, constituent-gapped-finite-groups-closed-under-products]
---

Suppose `(φ_k, ρ_k)` is a finite-group hyperlinear model of `S` with `Q_k^{(L)} ∈ 𝒢_θ`.

**Step 1 (push into `Q_k^{(L)}`).**
- `S` is nonabelian simple, hence perfect, so `S = S^{(L)}`.
- For each `x ∈ X` choose a word `v_x` in the `L`-th derived subgroup `F(X)^{(L)}` of the free group, with `v̄_x = x̄` in `S`:
  - write `x̄` as a product of commutators of elements of `S`;
  - write each of those elements as a product of commutators;
  - repeat `L` times, and spell out the result as a word.
- Evaluating a word of `F(X)^{(L)}` in any group lands in its `L`-th derived subgroup, so `φ'_k(x) := W_k(v_x) ∈ Q_k^{(L)}`.
- By Step 0 of `fp-simple-models-concentrate-on-template-constituents-proof`,
  `lim_ω ‖ρ_k(φ'_k(x)) − π_k(x̄)‖_2 = 0`. So `x ↦ (ρ_k(φ'_k(x)))_ω` induces the same injective homomorphism `Π`.
- The restriction of `ρ_k` to `Q_k^{(L)}` is a unitary representation. So `(φ'_k, ρ_k|_{Q_k^{(L)}})` is a finite-group
  hyperlinear model of `S` through the groups `Q_k^{(L)}`.

**Step 2 (no template constituents).** Every irreducible representation of `Q_k^{(L)} ∈ 𝒢_θ` is θ-gapped, so
`T_k(θ, D)` is empty for every `D`. This contradicts Corollary 2 of `fp-simple-models-concentrate-on-template-constituents`.

**Instances.**
- `L = 0`: by `constituent-gapped-finite-groups-closed-under-products` (a)–(c), quotients of products of quasisimple classical
  groups and abelian groups lie in `𝒢_{2^{−1/481}}`.
- `L = 4`, products of general linear groups: `(∏ G_i)^{(j)} = ∏ G_i^{(j)}`. For non-exceptional `(N,q)`,
  `GL_N(q)^{(j)} = SL_N(q)` for `j ≥ 1`, and it is quasisimple. `GL_2(2)^{(2)} = 1` and `GL_2(3)^{(4)} = 1`. So `Q_k^{(4)}` is a
  product of quasisimple classical groups, and it lies in `𝒢_{2^{−1/481}}`.
- *Sofic.* A sofic model through actions of `Q_k` on finite sets is a finite-group hyperlinear model with permutation
  representations: the normalized Hamming distance to `1` dominates `‖·‖_2²/2`, and an injective sofic model gives an
  injective trace-metric homomorphism. ∎
