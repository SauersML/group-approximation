---
rg: 2
id: khanh-acyclicity-and-steinberg-criteria
kind: claim
title: Khanh's acyclicity and Steinberg comparison criteria, with the ring-general GE, refinement and finite presentation theorems they use
distinct_from:
  leavitt-steinberg-map-iso-from-rank-three: that is Khanh's conclusion for the binary Leavitt algebra itself; this is the family of general criteria and cited ring-theoretic theorems his proof runs through, stated for arbitrary rings and algebras, which is what a transfer to other coefficient rings consumes.
  steinberg-finite-presentation-and-kazhdan-theorem: that pins an imported finite-presentation and property (T) result to one Steinberg source group in the Chatterji--Kassabov construction; this bundles Khanh's homology and comparison criteria with the general ring theorems, including Krstić--McCool, as quoted in his proof.
artifacts:
  - research/artifacts/boone-higman-leavitt-tensor-hosts-2026-09-12.md
  - research/artifacts/review-boone-higman-leavitt-tensor-hosts-2026-09-12.md
---

**ESTABLISHED (literature import).** These are the general statements used by
`leavitt-tensor-hosts-khanh-transfer-proof` and
`prime-field-leavitt-tensor-hosts-proof`. Source: H. V. Khanh, arXiv:2609.08428v1,
read from the PDF text on MSI (`lit-groups/khanh-clean.txt`) on 2026-09-12.

1. **Theorem 2.2 (acyclicity criterion).** "Suppose that A^2 ≅ A as right
   A-modules. Assume also that: (1) for every n > 0, the standard inclusion
   Γ_(n+2) -> Γ_(n+3) ... induces zero on H_n(−, Z); (2) H̃_i(X_r(A), Z) = 0 for
   0 <= i <= r−3 and r >= 4. Then H_n(A^x, Z) = 0 for every n > 0."
   - It is stated for nonzero unital `F_2`-algebras.
   - Its proof uses (1) only in degree `n`, through Lemma 2.4 with `k = 1`,
     `q = n+2`, and (2) only at `r = n+3`.
   - Lemmas 2.3 and 2.4, the scalar weight calculation, are part of this item.
2. **Theorem 5.1 (Steinberg comparison criterion).** "Let B be a nonzero unital
   ring of characteristic two, and fix n >= 4. Suppose that (1) GL_(n−1)(B) =
   E_(n−1)(B) and GL_(n−2)(B) = E_(n−2)(B); (2) j_(n−1)(N_(n−1)(B)) = 1 in
   St_n(B); (3) |X_n(B)| is simply connected. Then φ_n : St_n(B) -> GL_n(B) is
   an isomorphism." The proof applies Brown's presentation theorem (JPAA 32,
   1984) to the ordered frame complex.
3. **Lemma 5.2.** "For any unital ring B and m >= 3, j_m(N_m(B)) is central in
   St_(m+1)(B)."
4. **GE for simple rings with strong division.** Quoted in the proof of Lemma 5.3,
   after Menal--Moncasi (JPAA 33, 1984, Theorem 2.2 and the remark after
   Corollary 2.3): the remark "applies to a simple ring in which each nonzero x
   admits y, z with yxz = 1, and requires no regularity assumption". So every
   invertible matrix over such a ring is a product of elementary and invertible
   diagonal matrices.
5. **Voronetsky's refinement** (JPAA 225, 2021, §4 Proposition 1, used through
   arXiv:2004.08551v2). As applied in the proof of Theorem 5.4, it needs only
   coordinate maps `T_r, U_r` with `U_r T_r = I`, `T_r U_r = I`, built from
   `e, f, e*, f*`, and "requires no hypothesis on stable rank, quasi-finiteness,
   or centrality of the kernel".
6. **Krstić--McCool Theorem 3** (JPAA 141, 1999), as quoted in Theorem 6.1:
   "St_n(B) is finitely presented for every finitely presented associative
   unital ring B and every n >= 4".

Scope: items 1, 2 and 4--6 were checked as statements against the source text.
Their proofs were read in `review-boone-higman-leavitt-tensor-hosts-2026-09-12`
and not refereed.
