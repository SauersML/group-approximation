---
rg: 2
id: subshift-elementary-group-rigid-supports-are-mutual-centralizers
kind: claim
title: In EL_3 over a minimal subshift algebra over F_2, subgroups supported on complementary clopen sets are mutual centralizers, and the diagonal subgroup is the intersection of their normalizers
artifacts:
  - research/artifacts/sk-rigidity-intrinsic-reconstruction-2026-09-13-part1.md
---

**Setting.**
- `X` is an infinite minimal subshift with shift `T`, `A = LC(X,F_2)`, and `R = A ⋊_T Z`.
- `G = EL_3(R)`, `L = GL_3(A) = LC(X, GL_3(F_2)) ≤ G`, and `D = A·I_3`.
- For clopen `U`, `E_U = e_U I_3` and `G_U = G ∩ (I_3 + M_3(e_U R e_U))`, the elements of `G` supported in `U`.
- `L_V = {l ∈ L : l ≡ I_3 off V}`.

Then:
1. `span_(F_2){g − I : g ∈ G_U} = M_3(e_U R e_U)`, and `Z(e_U R e_U) = F_2·e_U`.
2. `C_G(G_U) = G_(X∖U)`.
3. `C_G(L_(X∖U)) = G_U`.
4. `N_G(G_U)` is the set of elements of `G` commuting with `E_U`, and `⋂_U N_G(G_U) = L`.
5. `N_G(L)` normalizes `D`. Conjugation induces homeomorphisms of `X` forming a group `Γ_X` with
   `[[T]]' ≤ Γ_X ≤ [[T]]`, the topological full group and its commutator subgroup. For `g ∈ N_G(L)` with homeomorphism
   `φ`, `g L_V g^(-1) = L_(φ(V))`.

The upper bound in 5 uses only that `g ∈ GL_3(R)` normalizes `D`. The lower bound uses the Whitehead lemma
`diag(a,a^(-1),1) ∈ E_3(R)`, so that `diag(a,a,a) ∈ G` for `a` in the commutator subgroup of the units, in particular
for the units `a_γ = Σ e_(γV_i) u^(n_i)`, `γ ∈ [[T]]'`.

Status: proved in `subshift-el3-rigid-supports-proof`, unreviewed.

**Review (sk-verify-3, 2026-09-13): PASS.** C1–C5 re-derived, including the corner centre, maximal commutativity of `LC(U)`, and `[[T]]' ≤ Γ_X ≤ [[T]]`. See `research/artifacts/sk-review-3-2026-09-13-part3.md` §B.
