---
rg: 2
id: kazhdan-fd-block-algebras-not-exact-proof
kind: route
title: The Kazhdan projection of rho tensor conjugate-rho dies in the quotient by the block ideal but not in the tensor ideal
target: kazhdan-fd-block-representation-algebras-are-not-exact
requires: []
---

Full proof: `research/artifacts/uct-ozawa-leg-exactness-2026-09-12.md` §2.

1. **Reduce to pairwise inequivalent blocks.** Multiplicities do not change the
   generated algebra, and exactness passes to quotients. Write
   `D = C*(⊕_j σ_j(G)) ⊂ ∏_j M_{n_j}`, with the `σ_j` irreducible and pairwise
   inequivalent. Put `B = ∏_j B(H̄_j)` and `J = ⊕_j B(H̄_j)`.
2. **Spectral gap.** With Kazhdan constant `κ` for a finite symmetric set `E`, every
   unitary representation `τ` has `spec(Σ_{s∈E} τ(s)) ⊂ [−|E|, |E| − κ²/2] ∪ {|E|}`.
   The `|E|`-eigenspace is the space of invariant vectors.
3. **Kazhdan projection.** For `x = Σ_s ρ(s) ⊗ ρ̄(s) ∈ D ⊙ B`, `q = f(x) ∈ D ⊗_min B`
   is, on each summand `H_j ⊗ H̄_k`, the projection onto invariant vectors of
   `σ_j ⊗ σ̄_k`. By Schur's lemma that is 0 for `j ≠ k` and the maximally entangled
   projection `P_{ξ_j}` for `j = k`.
4. **Not in the tensor ideal.** Every `y ∈ D ⊗_min J` satisfies
   `‖y(1 ⊗ (1 − P_K))‖ → 0`, with `P_K` the projection onto blocks `≤ K`. But
   `q(1 ⊗ (1 − P_K)) = ⊕_{k>K} P_{ξ_k}` has norm 1.
5. **Zero in the quotient.** `D ⊗_min Y → ∏_j M_{n_j} ⊗_min Y` is isometric, because
   spatial tensors commute with the central block projections of `D`. The `j`-th
   component of `q` lies in `M_{n_j} ⊗ B(H̄_j) ⊂ M_{n_j} ⊗ J`, so `q ↦ 0` in
   `D ⊗_min (B/J)`.
6. **Conclusion.** `q ∈ ker(D ⊗_min B → D ⊗_min B/J) \ D ⊗_min J`, so the tensor
   sequence is not exact and `D` is not exact.
7. **Instance.** Ozawa's `π_k` are irreducible (strong approximation onto `SL(3,F_p)`,
   2-transitive on `P²(F_p)`) and pairwise inequivalent (dimensions `p² + p`), and
   `SL(3,Z)` has (T). The conjugate algebra follows by the same argument.
