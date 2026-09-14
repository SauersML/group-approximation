---
rg: 2
id: singer-identities-make-subshift-el3-isos-standard-proof
kind: route
title: Singer identities kill mixed Frobenius pieces, Ext¹(3,3) = 0 makes R_Y³ the natural module tensor a free module, scalar supports give the diagonal, and bicommutants plus generation give the root subgroups
target: singer-identities-make-subshift-el3-isos-standard
requires:
  - frobenius-support-idempotents-give-boolean-realization
  - subshift-gl3-index-kernel-is-elementary-group
  - el3-root-subgroups-are-bicommutant-closed
  - peirce-root-homomorphisms-of-e3-are-standard
  - cantor-crossed-product-matrix-ring-iso-forces-soe
  - cantor-crossed-product-idempotents-similar-to-clopen-ones
  - minimal-cantor-crossed-products-have-internal-cancellation
  - subshift-crossed-product-k0-is-coinvariant-group
  - subshift-elementary-group-rigid-supports-are-mutual-centralizers
artifacts:
  - research/artifacts/sk-orthogonality-o-2026-09-14-part1.md
---

Full proof: `research/artifacts/sk-orthogonality-o-2026-09-14-part1.md` §§0–3.

1. **Representation facts (§1).**
   - Over `F_2`, the simple modules of `F21` are `1, 2, 3, 3*`.
   - `8|_{F21} = 2⊕3⊕3*`.
   - `3⊗3* = 1⊕8`, so `Ext¹_{F_2GL_3(2)}(3,3) = 0`.
   - On the diagonal, `3⊗3` restricts to `3⊕3*⊕3*`.
   - (Sing_V) says that `α(F21_V)` has type `3` on `S_VM`.
2. **Orthogonality.** For disjoint `V, W`, the piece `S_VS_WM` has type `(3,3)`, and its diagonal type contains `3*`,
   which (Sing_{V⊔W}) forbids.
3. **Module type.** (O′) and (Sing_X) leave only composition factor `3` for `α(GL_3(F_2)_X)` on `M = R_Y³`.
   - F4 makes `M` semisimple, so `M ≅ 3 ⊗ P` with `P³ ≅ R_Y³`.
   - `K_0` is torsion-free, Theorem DP holds, and (Div) with Theorem IC gives `P ≅ R_Y`. This yields `k ∈ GL_3(R_Y)` with
     `k^{-1}α(q_X)k = q`.
   - `G_Y ⊴ GL_3(R_Y)` because `G_Y = ker(ind)`.
4. **Scalar supports.** `k^{-1}S_Vk` commutes with the constant `F21`, whose span is `M_3(F_2)`. So it is `b_VI`.
   - Proposition F item 2 gives `k^{-1}α(q_V)k = I + b_V(q−I)`.
   - So the diagonal maps onto `GL_3(𝔅′)`.
5. **Roots.** `α′(A_ij(R_X)) = CC(T_ij(𝔅′)) ⊆ A_ij(R_Y)` by the bicommutant theorem.
   - Commutator relations and `1 ∈ J_ij` make all `J_ij` one subring `J`.
   - `α′` is surjective, so `J = R_Y`.
6. **Standardness.** Theorem P with `E_k = E_kk`, then SOE from the matrix-ring isomorphism.
