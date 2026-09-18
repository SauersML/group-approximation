---
rg: 2
id: cover-pair-sections-localize-to-the-symmetric-locus-proof
kind: route
title: Lift only where the seed is wrong; off the symmetric locus the wrong set is compact and E-free, so a finite clopen greedy colouring schedules the lifts continuously
target: cover-pair-sections-localize-to-the-symmetric-locus
requires:
  - post-surjective-sft-covers-admit-scheduled-sections
  - strict-pairs-give-dual-failures-on-bounded-defect-domains
artifacts:
  - research/artifacts/symmetric-locus-seeds-2026-09-18.md
---

A complete, elementary proof, in Section 1 of the artifact. Corollaries are in Section 2.

1. **Exact set.** `V = {w : F(ξ(w))(1) = w(1)}` is clopen and contains `Sym_E`. By equivariance,
   `g^-1 . z ∈ V` implies `F(ξ(z))(g) = z(g)`.
2. **Clopen colouring.** `K = A^G \ V` is compact, and `e . w ≠ w` on `K` for `e ∈ E \ {1}`. Clopen sets
   `U_w` with `U_w ∩ e . U_w = ∅` have a finite subcover. A greedy colouring over the induced finite clopen
   partition has depth `m`, so it is continuous and proper for `E`.
3. **Schedule.** The colour classes `S_i(z) = {g : g^-1 . z ∈ K, c(g^-1 . z) = i}` are `E`-separated. Apply
   Lemma 2 of the scheduled-sections artifact to each class in turn, starting from `ξ(z)`.
4. **Verification.** Lemma 2 changes outputs only on the class it lifts, and exact sites are never touched.
   Equivariance and continuity follow as in Theorem A(3).

Both prerequisites are ESTABLISHED.
- `post-surjective-sft-covers-admit-scheduled-sections` supplies Lemmas 1–2 (local and separated lifts) and
  Proposition C (a section is an injective non-surjective automaton), which are used in Theorem S and Corollary S1.
- `strict-pairs-give-dual-failures-on-bounded-defect-domains` supplies the cover pair `(X_R, σ|_{X_R})` with
  seed `τ`. It is used only for the ⇒ direction of Corollary S1.
