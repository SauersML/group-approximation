---
rg: 2
id: rf-free-minimal-zn-non-fp-proof
kind: route
title: Ma's LEF theorem for residually finite actions, plus Matui's simplicity, plus the Gordon–Vershik fact that a finitely presented LEF group is residually finite
target: rf-free-minimal-zn-actions-have-non-fp-derived-full-groups
requires: []
---

## Inputs

- **(Ma)** Xin Ma, "Soficity, amenability, and LEF-ness for topological full groups", arXiv:2209.00580. Read at source
  (PDF text, 2026-09-18).
  - **Definition 5.1** (from Kerr–Nowak [17, §2]): "A continuous action of G on a perfect compact metrizable space X,
    equipped with a compatible metric d, is said to be residually finite if for any finite F ⊂ G and ε > 0, there is a
    finite set E ⊂ X, equipped with a G-action β such that E is ε-dense in X and d(α(s)(z), β(s)(z)) < ε for all z ∈ E
    and s ∈ F."
  - **Theorem 5.5:** "Let α : G ↷ X be a minimal topologically free residually finite action of a countable discrete
    group G on the Cantor set X. Then its topological full group [[α]] is LEF."
  - **Remark 5.6:** every minimal `Z`-action on the Cantor set is residually finite (Pimsner; Kerr–Nowak Prop. 7.1).
- **(VG)** Vershik–Gordon, "Groups that are locally embeddable in the class of finite groups", St. Petersburg Math. J.
  9 (1998). A finitely presented LEF group is residually finite. Cited, not re-read. The proof is short: map a finite
  presentation's relators, together with any finite set of elements, into a finite group through LEF.
- **(Matui)** For a minimal essentially principal ample groupoid on the Cantor set, `D([[G]])` is simple (Matui, Proc.
  LMS 104 (2012), Thm 4.7; cited, not re-read). It is nontrivial and infinite, since it contains 3-cycles of
  arbitrarily small clopen sets.

## Proof

1. **LEF.** A free action is topologically free, so (Ma) Thm 5.5 applies and `[[φ]]` is LEF. LEF passes to subgroups:
   restrict the local models to the finite subsets of the subgroup. So `D([[φ]])` is LEF.
2. **Not finitely presented.** Suppose `D = D([[φ]])` were finitely presented. By (VG) it would be residually finite.
   But `D` is simple and infinite by (Matui), so it has no proper finite-index normal subgroup other than the trivial
   one, and it is not residually finite. Contradiction. If `D` is not finitely generated, it is not finitely presented
   either.
3. **Products are residually finite.** Let `(X_i, φ_i)` be minimal Cantor `Z`-systems, `X = ∏ X_i` with the max
   metric, and `s ∈ Z^N` acting by `φ(s) = ∏ φ_i^(s_i)`.
   - **Free.** Each `φ_i` is aperiodic, since it is minimal on an infinite space, so `s` fixes a point only if every
     `s_i = 0`.
   - **Minimal.** The orbit closure of `(x_i)` contains `∏ (orbit closure of x_i) = X`.
   - **Residually finite.** Given `F` and `ε`, apply Remark 5.6 to each `φ_i` with the finite set
     `{s_i : s ∈ F} ⊆ Z` and `ε`. This gives `E_i ⊆ X_i` and `Z`-actions `β_i`. Then `E = ∏ E_i` with
     `β(s) = ∏ β_i^(s_i)` is a `Z^N`-action, `E` is `ε`-dense, and
     `d(φ(s)z, β(s)z) = max_i d(φ_i^(s_i) z_i, β_i^(s_i) z_i) < ε`.
4. **Odometers are residually finite.** Let `X = lim Z^N/L_k`, `x_0` the identity, and `U_k` the kernel of
   `X → Z^N/L_k`, which is open and shrinks to the identity.
   - Fix a set of coset representatives `R_k` of `L_k` and put `E = {t·x_0 : t ∈ R_k}`, with
     `β(s)(t x_0) = ((t + s) mod L_k) x_0`.
   - `β(s)(t x_0)` and `φ(s)(t x_0)` differ by an element of the image of `L_k`, which lies in `U_k`, so they are close
     for large `k`.
   - `E` is `U_k`-dense. Freeness holds by trivial intersection of the `L_k`, and minimality because `Z^N` is dense. ∎
