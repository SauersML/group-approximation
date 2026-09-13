---
rg: 2
id: induced-actions-sofic-iff-homogeneous-action-sofic-proof
kind: route
title: The induced action is stably orbit equivalent to the product of the homogeneous action with the seed, and products of sofic actions are sofic
target: induced-actions-sofic-iff-homogeneous-action-sofic
requires:
  - paunescu-sofic-action-class-permanence
  - sofic-free-actions-are-soe-invariant
  - cordeiro-sofic-relation-permanence
artifacts:
  - research/artifacts/nonsofic-action-mixing-transfer-part2-2026-09-12.md
---

**(2 ⇒ 1).** Take `Z` to be the one-point action. Then `H ×_Γ Z = H/Γ`.

**Product lemma.** If `Γ ↷ X_1` and `Γ ↷ X_2` are sofic, so is the diagonal action on `X_1 × X_2`.
Let `Θ_i : L^∞(X_i) ⋊ Γ → Π_{k→𝒰} M_{n_{i,k}}` be sofic embeddings with `σ_i(g) = Θ_i(u_g)`. On the
algebraic crossed product put

```text
Θ(f_1 ⊗ f_2) = Θ_1(f_1) ⊗ Θ_2(f_2),      Θ(u_g) = σ_1(g) ⊗ σ_2(g)      in  Π_{k→𝒰} M_{n_{1,k} n_{2,k}}.
```

Normalized traces multiply under tensor products, so

`tr(Θ((f_1⊗f_2) u_g)) = τ_1(f_1 u_g) τ_2(f_2 u_g) = δ_{g,1} ∫f_1 ∫f_2`,

which is the canonical trace. Covariance holds factorwise. Tensor products of diagonal matrices are
diagonal, and tensor products of permutation matrices are permutation matrices. So `Θ` extends to a
sofic embedding. (Alpeev, arXiv:1706.01864, Theorem 4.2, verbatim from the PDF: *"Direct product of two
sofic actions of sofic group on standard probability spaces is a sofic action."*)

**(1 ⇒ 2).** Let `Γ ↷ Z` be sofic with `W = H ×_Γ Z` essentially free. On `Ω = H × Z` let `Γ_ℓ` act by
`γ·(h,z) = (γh, z)` and `Γ_r` by `γ∗(h,z) = (hγ^(−1), γz)`. They commute and preserve Haar ⊗ ζ (`H` is
unimodular), with finite-measure fundamental domains `X_r = D × Z` for `Γ_r` and `X_ℓ = D' × Z` for
`Γ_ℓ` (part 2 artifact, Step 2).

* `Ω/Γ_r = W` with the `Γ_ℓ`-action, and `Γ_ℓ\Ω = V = Γ\H × Z` with `Γ_r` acting diagonally.
* `Γ ↷ Γ\H`, `Γh ↦ Γhγ^(−1)`, is isomorphic via `Γh ↦ h^(−1)Γ` to the left action on `H/Γ`. So it is
  sofic by 1 and essentially free, and `V` is essentially free.
* By the product lemma `V` is sofic, so its orbit relation is sofic (Păunescu Proposition 1.15).

Let `E` be the orbit relation of `Γ_ℓ × Γ_r` on `Ω` and `X = X_ℓ ∪ X_r`. Then `E|_{X_ℓ} ≅ R(V)` and
`E|_{X_r} ≅ R(W)`, and both domains meet almost every class of `E|_X`. By amplification (part 1 of
`sofic-free-actions-are-soe-invariant`), `E|_X` is sofic. By restriction (Cordeiro Proposition 3.2(a),
`cordeiro-sofic-relation-permanence`), `E|_{X_r} = R(W)` is sofic. `W` is essentially free, so it is sofic
by Proposition 1.15. ∎

**Freeness for `SL_3(R)/SL_3(Z)`.** `γ·gΓ = gΓ` iff `g^(−1)γg ∈ Γ`. For fixed `δ ∈ Γ`, the set
`{g : γg = gδ}` is empty or a coset `g_0 C(δ)` of the centralizer of `δ` in `SL_3(R)`, a proper closed
subgroup for `δ != 1`, since `SL_3(Z)` has trivial center. It is a lower-dimensional submanifold, hence
Haar null, and the union over countably many `δ` is null.
