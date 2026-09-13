---
rg: 2
id: abc-twisted-laurent-k-theory-fibration
kind: claim
title: Ara–Brustenga–Cortiñas Theorem 3.6 and Lemma 7.2 — the Pimsner–Voiculescu fibration for crossed products by Z, with vanishing twisted NK over regular supercoherent rings
distinct_from:
  abc-leavitt-path-k-theory-exact-sequence: that imports ABC Theorem 7.6 (the 1 − N^t sequence for Leavitt path algebras); this imports the general corner skew Laurent fibration (Theorem 3.6), its crossed-product case, and the NK vanishing lemma (Lemma 7.2) used to prove it
artifacts:
  - research/artifacts/un-orbit-equivalence-2026-09-13-part2.md
---

**ESTABLISHED by citation** (`abc-twisted-laurent-k-theory-fibration-citation`). P. Ara, M. Brustenga, G. Cortiñas,
*K-theory of Leavitt path algebras*, Münster J. Math. 2 (2009), arXiv:0903.0056v2. Read on 2026-09-13 from the
extracted text on MSI (`/projects/standard/hsiehph/sauer354/lit-groups/abc-clean.txt`, lines 389–398, 399–401,
941–957, 1017–1026). The extraction drops Greek letters, ⊗, ± and arrows. Below, those glyphs are restored from
context and marked [·]; every word is verbatim.

- **Theorem 3.6.** "Let R be a unital ring and let A be a ring. Let [σ] : R → pRp be a corner-isomorphism. Assume
  that R[⊗]A is H-unital. Then there is a homotopy fibration of nonconnective spectra K(R[⊗]A) → K(R[⊗]A) [⊕]
  NK(R[⊗]A;[σ⊗1])[_+] [⊕] NK(R[⊗]A;[σ⊗1])[_−] → K((R[⊗]A)[t+;t−;σ⊗1]). In other words,
  K((R[⊗]A)[t+;t−;σ⊗1]) = NK(R[⊗]A;[σ⊗1])[_+] [⊕] NK(R[⊗]A;[σ⊗1])[_−] [⊕] hocofiber(K(R[⊗]A) [→(1−σ⊗1)] K(R[⊗]A))."
- **Proof, Step 1.** "Assume that [σ] is a unital isomorphism and A = Z. In this case the skew Laurent polynomial ring
  is the crossed product by Z; R[t+;t−;σ] = R[t;t^{−1};σ]."
- **Lemma 7.2.** "Let R be a regular supercoherent ring and let [α] be an automorphism of R. Extend [α] to an
  automorphism of R[t_1;t_1^{−1};...;t_p;t_p^{−1}] by [α](t_i) = t_i. Then NK_n(R[t_1;t_1^{−1};...;t_p;t_p^{−1}];[α]) = 0
  for every p ≥ 0 and every n ∈ Z."
- **Definitions (§7).** "Recall that a unital ring R is said to be coherent if its finitely presented modules form an
  abelian subcategory of the category of all modules. We say that R is regular coherent if it is coherent and in
  addition any finitely presented module has finite projective dimension. [...] The ring R is called supercoherent in
  case all polynomial rings R[t_1;...;t_p] are coherent".
- **Colimits (proof of Lemma 3.5).** "the fact that K-theory preserves filtering colimits (see [31, IV.6] for the unital
  case [...])".

**Consequence used downstream.** For a unital regular supercoherent ring R and a unital automorphism σ, Theorem 3.6
with A = Z and Lemma 7.2 give `K(R[t,t^{−1};σ]) = hocofiber(1 − σ_*)`. So there is a long exact sequence
`K_n(R) →(1−σ_*) K_n(R) → K_n(R[t,t^{−1};σ]) → K_(n−1)(R) → ...`.
