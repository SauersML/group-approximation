---
rg: 2
id: minimal-cantor-crossed-products-stabilize-laurent-pairs
kind: claim
title: In LC(X,F) ⋊ Z for a minimal Cantor system, aR + qR = R with q a nonzero Laurent polynomial in u implies a + qc is a unit for some c
distinct_from:
  minimal-cantor-crossed-product-has-stable-rank-at-most-two: that asks for Bass stable rank ≤ 2 (or 1) for all unimodular rows; this proves the stable-rank-one completion for every pair whose second entry is a Laurent polynomial in u.
artifacts:
  - research/artifacts/sk-algebraic-putnam-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).** Let `(X,T)` be a minimal homeomorphism of the Cantor set, `F` a field and `R = LC(X,F) ⋊_T Z`. Let `a ∈ R` and `0 ≠ q ∈ F[u^{±1}]` with `aR + qR = R`. Then there is `c ∈ R` with `a + qc ∈ R^×`.

The unit can be chosen in `GL_1(A_𝒫)` for a Kakutani–Rokhlin tower algebra `A_𝒫 ≅ ∏_a M_{h_a}(F)`.

**Corollary.** Every unimodular row `(p_1,…,p_n)` over `F[u^{±1}]` is stable in `R`. For `q = gcd(p_2,…,p_n)`, the pair `(p_1,q)` is coprime.

**Contrast.** Over `F_2`, the pair `(1+u, Φ_5(u))` is unimodular in `F_2[u^{±1}]`. No `1+u + Φ_5(u)c` with `c ∈ F_2[u^{±1}]` is a unit, since `1+ū ∉ ⟨ū⟩ ⊆ F_16^×`. So the stable-rank-2 obstruction of `F[u^{±1}]` disappears in `R`.

**Proof outline.**
- Residues `ρ_q∘a∘r = ρ_q` show that the block columns of `a` already span `F[u]/(q_0)`.
- On each tower block, an invertible `G` with the same residues as `a` exists and depends only on local data.
- `g = ⊕G` is a unit of `A_𝒫`. The columns of `g − a` lie in `qV`, so `g − a = qc` by `laurent-right-ideals-of-cantor-crossed-products-columnwise`.

**Review (sk-verify-16, 2026-09-13): PASS.** Re-derived:
- ρ_q∘a∘r = ρ_q, and ψ_0 is onto from ≥ d interior positions (h ≥ 2w_r+d+2);
- G ∈ GL_h(F) with φ_0∘G = ψ_0;
- g = ⊕G ∈ GL_1(A_𝒫) with columns of g−a in qV.
The (1+u, Φ_5) model test is correct. See `research/artifacts/sk-verify-16-2026-09-13-part2.md` §5.
