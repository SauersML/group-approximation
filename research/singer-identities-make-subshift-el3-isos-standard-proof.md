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
  - research/artifacts/sk-verify-25a-2026-09-14.md
  - research/artifacts/sk-verify-25b-2026-09-14.md
---

Full proof: `research/artifacts/sk-orthogonality-o-2026-09-14-part1.md` §§0–3, with the fixes of sk-verify-25a and
sk-verify-25b merged (both PASS-WITH-FIXES, independent).

1. **Representation facts (§1).**
   - Over `F_2`, the simple modules of `F21` are `1, 2, 3, 3*`.
   - `8|_{F21} = 2⊕3⊕3*`.
   - `3⊗3* = 1⊕8`, so `Ext¹_{F_2GL_3(2)}(3,3) = 0`.
   - On the diagonal, `3⊗3` restricts to `3⊕3*⊕3*`.
   - (Sing_V) says that `α(F21_V)` has type `3` on `S_VM`.
2. **Orthogonality.** For disjoint `V, W`, the piece `S_VS_WM` has type `(3,3)`, and its diagonal type contains `3*`,
   which (Sing_{V⊔W}) forbids.
3. **Module type.** (O′) and (Sing_X) leave only composition factor `3` for `α(GL_3(F_2)_X)` on `M = R_Y³`.
   Restriction to `F21_X` is semisimple since 21 is odd, so a forbidden constituent would be a summand of `M` under
   `K_X` (Fix A3).
   - F4 makes `M` semisimple, so `M ≅ 3 ⊗ P` with `P³ ≅ R_Y³`.
   - `K_0` is torsion-free, Theorem DP holds, and (Div) with Theorem IC gives `P ≅ R_Y`. This yields `k ∈ GL_3(R_Y)` with
     `k^{-1}α(q_X)k = q`.
   - `G_Y ⊴ GL_3(R_Y)` because `G_Y = ker(ind)` (index kernel theorem, sk-verify-18 part6 PASS).
4. **Scalar supports.** `k^{-1}S_Vk` commutes with the constant `F21`, whose span is `M_3(F_2)`. So it is `b_VI`, and
   Proposition F (items 1–2 of the normalizer artifact; item 3 of `frobenius-support-idempotents-give-boolean-realization`,
   Fix W5) makes `V ↦ b_V` a Boolean embedding.
   - **The diagonal (Fix A2).** By (O) and (O′), `S_{X∖V} = I − S_V`. `α(Q_V)` commutes with `K_{X∖V}`, so it preserves
     `S_VM` and `(I−S_V)M = Fix(K_V)`. The kernel of its action on `Fix(K_V)` is normal in `α(Q_V) ≅ GL_3(2)`, which is
     simple, and contains `K_V ≠ 1`. So `α(q_V) − I = S_V(α(q_V) − I)S_V`, and `k^{-1}α(q_V)k = I + b_V(q−I)`.
   - So the diagonal maps onto `GL_3(𝔅′)`.
5. **Roots (Fix W2).** `C_{G_X}(A_ij ∩ L_X) = C_{G_X}(A_ij(R_X))`, since commuting with every `I + fE_ij`, `f ∈ D_X`,
   forces `g_ii = g_jj ∈ D_X`, an invertible idempotent, hence 1. Item 2 of `el3-root-subgroups-are-bicommutant-closed`
   gives `CC(A_ij ∩ L_X) = A_ij(R_X)`. Then `α′(A_ij(R_X)) = CC(T_ij(𝔅′)) ⊆ A_ij(R_Y)`.
   - Commutator relations and `1 ∈ J_ij` make all `J_ij` one subring `J`.
   - `α′` is surjective, so `J = R_Y`.
6. **Standardness (Fix W3).** Write `α′(e_ij(r)) = e_ij(φ_ij(r))`. `φ_ij(1) = 1` because `α′` fixes `e_ij(1)`, and
   `φ_ik(rs) = φ_ij(r)φ_jk(s)` with `s = 1`, `r = 1` forces all `φ_ij` equal to one ring isomorphism `φ: R_X → R_Y`. So
   `α′ = M_3(φ)|_{G_X}`, and `cantor-crossed-product-matrix-ring-iso-forces-soe` with `m = 1` gives strong orbit
   equivalence. `peirce-root-homomorphisms-of-e3-are-standard` with `E_k = E_kk` gives the same.
