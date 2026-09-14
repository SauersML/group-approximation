---
rg: 2
id: frobenius-bicommutants-make-subshift-el3-isos-standard-proof
kind: route
title: Torsion lies in EL_3, so the Y-side double centralizer of a Frobenius image contains a full GL_3(2) per isotypic block; its order is 168, which kills type 2 and mixed types, and non-semisimplicity of 3⊗3 plus the trivial centralizer give (O) and (O′)
target: frobenius-bicommutants-make-subshift-el3-isos-standard
requires:
  - subshift-gl3-index-kernel-is-elementary-group
  - subshift-elementary-group-rigid-supports-are-mutual-centralizers
  - frobenius-support-idempotents-give-boolean-realization
  - singer-identities-make-subshift-el3-isos-standard
  - cantor-crossed-product-idempotents-similar-to-clopen-ones
  - minimal-subshift-algebra-is-simple-lef-ring
artifacts:
  - research/artifacts/sk-orthogonality-o-2026-09-14-part2.md
  - research/artifacts/sk-verify-25a-2026-09-14.md
  - research/artifacts/sk-verify-25b-2026-09-14.md
---

Full proof: `research/artifacts/sk-orthogonality-o-2026-09-14-part2.md`, with the fixes of sk-verify-25a and
sk-verify-25b merged (both PASS-WITH-FIXES, independent). The unused `requires` entry
`diagonal-recognition-makes-subshift-el3-isos-standard` was dropped (Fix C4).

1. **Lemma Z.** In a simple ring with centre `F`, an element commuting with both off-diagonal Peirce spaces of a
   nontrivial idempotent is central.
2. **Lemma X.**
   - `C_{G_X}(F21_V)` is the set of elements that are scalar units on `e_VM_X` and arbitrary on `e_{X∖V}M_X`.
   - It contains `G_{X∖V}`, and it contains the order-2 scalars `(e_V + n)I_3`, which lie in `G_X` by the index kernel
     theorem.
   - C2 and Lemma Z force the bicommutant down to `Q_V`. Lemma Z applies to `R_V = e_VR_Xe_V`, which is simple with
     centre `F_2e_V`: a corner of the simple ring `R_X` is simple and, `e_V` being full, `Z(e_VR_Xe_V) = e_VZ(R_X)`
     (Fix C2; no first-return corner isomorphism is needed).
3. **Theorem C.**
   - Elements of `C_{G_Y}(K_V)` are `id ⊗ End(P_t)` on each isotypic block `t ⊗ P_t`.
   - So `a ⊗ id` on one block (and multiplication by `ω` on the type-2 block) lies in `CC_{G_Y}(K_V)`: `g_t(a)` lies in
     `F_2I + span_{F_2}K_V`, since the `t`-component of `F_2[F21]` is `M_3(F_2)` (`F_4` for `t = 2`), so it commutes with
     `C_{G_Y}(K_V)` (Fix C3). It is torsion, so it lies in `G_Y`.
   - `CC_{G_Y}(K_V) = α(Q_V)` has order 168, so there is exactly one block and it carries all of `α(Q_V)`.
4. **(O).**
   - The joint piece of `V, W` is `t_V ⊠ t_W ⊗ P`.
   - On the diagonal, `3⊗3` is not semisimple (the symmetric square is a non-split extension of `3` by `Λ² ≅ 3*`), and
     `3⊗3* ⊇ 8`.
   - Theorem C at `V⊔W` then kills the piece.
5. **(O′).**
   - `α(L_X)` is trivial on `(I−S_X)M`.
   - Square-zero elements of that corner are torsion, so they lie in `G_Y`, and they centralize `α(L_X)`.
   - The centralizer is trivial, so the corner is zero.
6. **Orientation.** `α(Q_X)` acts on `S_VM` as `α(Q_V)`, so `t_V = t_X`.
7. **Theorem D (Fix W4).** If `t_X = 3*`, replace `α` by `α∘γ_X` and apply Theorem C and Corollaries O, O′ and T to it;
   its orientation is `3`, because `(α∘γ_X)(q_X) = α(γ(q)_X)` acts as `ψ_X(γ(q)) ⊗ id` and `3*∘γ ≅ 3`. Then the Singer
   identities hold, and `singer-identities-make-subshift-el3-isos-standard` gives `α = inn(k)∘M_3(φ)|_{G_X}` for a ring
   isomorphism `φ: R_X → R_Y`.
