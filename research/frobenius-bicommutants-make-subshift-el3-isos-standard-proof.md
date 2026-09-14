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
  - diagonal-recognition-makes-subshift-el3-isos-standard
  - cantor-crossed-product-idempotents-similar-to-clopen-ones
  - minimal-subshift-algebra-is-simple-lef-ring
artifacts:
  - research/artifacts/sk-orthogonality-o-2026-09-14-part2.md
---

Full proof: `research/artifacts/sk-orthogonality-o-2026-09-14-part2.md`.

1. **Lemma Z.** In a simple ring with centre `F`, an element commuting with both off-diagonal Peirce spaces of a
   nontrivial idempotent is central.
2. **Lemma X.**
   - `C_{G_X}(F21_V)` is the set of elements that are scalar units on `e_VM_X` and arbitrary on `e_{X∖V}M_X`.
   - It contains `G_{X∖V}`, and it contains the order-2 scalars `(e_V + n)I_3`, which lie in `G_X` by the index kernel
     theorem.
   - C2 and Lemma Z force the bicommutant down to `Q_V`.
3. **Theorem C.**
   - Elements of `C_{G_Y}(K_V)` are `id ⊗ End(P_t)` on each isotypic block `t ⊗ P_t`.
   - So `a ⊗ id` on one block (and multiplication by `ω` on the type-2 block) lies in `CC_{G_Y}(K_V)`. It is torsion,
     so it lies in `G_Y`.
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
7. **Theorem D.** After composing with `γ_X` if `t_X = 3*`, the Singer identities hold, and
   `singer-identities-make-subshift-el3-isos-standard` applies.
