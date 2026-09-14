---
rg: 2
id: subshift-gl3-index-kernel-is-elementary-group
kind: claim
title: Over the binary subshift ring the half-orbit index kernel in GL_3 is exactly EL_3, so GL_3(R_X) = G_X ⋊ Z and G_X is its commutator subgroup
distinct_from:
  crossed-product-gl-n-has-infinite-cyclic-index-quotient: that proves EL_n ⊆ ker(ind) and ind onto Z; this proves the converse ker(ind|GL_3) = EL_3 for infinite minimal X over F_2, with no stable-rank input
  subshift-el-groups-boundedly-elementary-generated: that is Theorem D for elements of G_X; this observes that its proof uses membership only through index zero at the cuts, and so applies to every index-zero element of GL_3
artifacts:
  - research/artifacts/sk-free-10-gl3-index-2026-09-14.md
---

**ESTABLISHED (reviewed: sk-verify-18 PASS, part6)** by `subshift-gl3-index-kernel-is-elementary-group-proof`.

**Statement.** Let (X,T) be an infinite minimal Cantor system, R = LC(X,F_2) ⋊_T Z, G_X = EL_3(R), d = diag(u,1,1), and ind: GL_3(R) → Z the half-orbit Fredholm index. Then:
- ind does not depend on the base point or the cut;
- ker(ind) = EL_3(R), and every index-zero element is a product of at most 78 elementary matrices;
- GL_3(R) = G_X ⋊ ⟨d⟩ with GL_3(R)/G_X ≅ Z;
- G_X = [GL_3(R), GL_3(R)];
- GL_3(R)/EL_3(R) → K_1(R) is injective. It is an isomorphism if K_1(R) ≅ Z (`binary-subshift-ring-k1-is-half-orbit-index`).

**Model tests.** diag(u,u,1) has index −2 and lies outside G_X; diag(u,u^{-1},1) has index 0 and lies in G_X (Whitehead); uI_3 has index −3.

**Scope.** Minimality and infiniteness enter the constancy of the index and the Kakutani–Rokhlin towers of Theorem D. The periodic case is not claimed.

## Review
- **sk-verify-18 PASS (2026-09-14, `research/artifacts/sk-verify-18-2026-09-14-part6.md`):** re-derived: Lemma 1 (cut, translation, local constancy, minimality); the check that Theorem D's proof uses membership in G only through (T2) at the choice dim M = dim K in (T3), so every index-zero h ∈ GL_3(R) factors as H_1H_2 over tower algebras; and (a)–(c). Conditional on the reviewed inputs (I1) and (I2).
- Consumed by the rigidity theorem `frobenius-bicommutants-make-subshift-el3-isos-standard`; its consumption was checked against this statement by sk-verify-25a and sk-verify-25b (2026-09-14). Status line updated by sk-rigidity-merge.
