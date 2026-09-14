---
rg: 2
id: cantor-crossed-product-idempotents-similar-to-clopen-ones
kind: claim
title: Every idempotent of M_n(LC(X,F) ⋊ Z), for a minimal Cantor system, is similar to a diagonal matrix of clopen indicators
distinct_from:
  minimal-cantor-crossed-product-is-an-exchange-ring: that asks whether every element has an exchange idempotent; this classifies the idempotents that exist, up to similarity.
  subshift-crossed-product-k0-is-coinvariant-group: that computes the Grothendieck group K_0; this is an unstable, similarity-level statement about individual idempotents, proved without K-theory.
artifacts:
  - research/artifacts/sk-algebraic-putnam-2026-09-13-part2.md
---

**ESTABLISHED (unreviewed).** Let `(X,T)` be a minimal homeomorphism of the Cantor set, `F` a field, `R = LC(X,F) ⋊_T Z`. Every idempotent `e ∈ M_n(R)` is similar, by a unit of `M_n(R)`, to `diag(e_{W_1},…,e_{W_n})` for clopen sets `W_i`. For `n = 1`: `e = he_Wh^{−1}` with `h ∈ R^×` and `W` clopen.

**Proof outline** (artifact §2–§3).
1. **One cut.** At a Kakutani–Rokhlin cut `c`, the range and kernel of `e` split off `E_± = eV ∩ V_±` and `E′_± = (1−e)V ∩ V_±`, with a complement `M` of dimension `≤ 2w` in the window around `c`. The images `Ĩ` of `eV` and `Ĩ′` of `(1−e)V` in `M` satisfy `M = Ĩ ⊕ Ĩ′`.
2. **Laplace step.** A Laplace expansion gives a coordinate subset `T` of the window basis with `span T ⊕ Ĩ′ = M` and `span(B∖T) ⊕ Ĩ = M`. This works over any field.
3. **Split idempotent.** The projection onto `E_− ⊕ E_+ ⊕ span T` along `E′_− ⊕ E′_+ ⊕ span(B∖T)` splits at `c`, differs from `e` only in the window, and is conjugate to `e` by the invertible intertwiner `1 + Δ_c(2e−1)`.
4. **All cuts.** Doing this at all cuts (local choices, disjoint windows) conjugates `e` into a tower algebra `∏_a M_{h_a}(F)`, where it is similar to a coordinate idempotent `e_W`.
