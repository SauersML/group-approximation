# Adversarial re-check: PBH closure under graph products and common-retract amalgams (bh-free-11, 2026-09-18)

Lane bh-free-11 of the BH swarm checked, step by step, the two nodes that claim to answer
Belk–Fournier-Facio–Hyde–Zaremsky (BFFHZ), arXiv:2503.21882v2, Question 3.1:

- `pbh-class-closed-under-graph-products` with route `pbh-graph-product-closure-proof`;
- `pbh-class-closed-under-common-retract-amalgams` with route `pbh-common-retract-amalgam-closure-proof`.

**Verdict: both proofs hold, given the three imported literature theorems below.** No gap was
found. This is one lane's check, not an external review.

## 1. Imports, re-read at source (arXiv HTML of 2503.21882v2, and the repo citation nodes)

- **BFFHZ Theorem C.** For a finitely generated group G with solvable word problem, these are
  equivalent: (i) G satisfies the permutational Boone–Higman conjecture; (ii) G embeds in a
  finitely presented twisted Brin–Thompson group; (iii) G embeds in a finitely presented simple
  highly transitive group; (iv) G embeds in a finitely presented simple MIF group.
- **BFFHZ Theorem E**, verbatim: "For any finitely presented simple MIF group G, the group
  Aut_G(G∗F_n) (n≥2) admits an action of type (A), and hence satisfies the (permutational)
  Boone–Higman conjecture."
  - Aut_G means automorphisms whose restriction to G is the identity. This is exactly the Ω of
    both routes.
  - Type (A) includes faithfulness in their definition, so every subgroup of Ω lies in B_A.
- **Zaremsky, arXiv:2405.18354, Proposition 5.5**, as quoted in BFFHZ: "PBH is stable under
  commensurability and direct products". This is the import behind the direct-product closure
  used in Step 0 and Step 1.

The hypotheses match. In the graph-product route, A ⊇ K × X carries a type (A) action. So A is
finitely presented with solvable word problem, (i) holds, and (iv) gives the finitely presented
simple MIF group H. In the common-retract route, the same applies to A_0 ⊇ Γ_X × Γ_Y ⊇ D. In both
routes, n = 2 in Theorem E.

## 2. Step checks (graph-product route; the common-retract route is the same argument)

- **Step 1.** ρ_a (a ∈ H∗⟨y⟩) is an automorphism with inverse ρ_{a^{-1}}. Also ρ_aρ_b = ρ_{ab},
  and ρ_a = id only if a = 1. Checked.
- **Step 2.** γ_c is an automorphism with inverse γ_{c^{-1}}. Composing on x gives x·cd, and on y
  gives (cd)^{-1} y (cd). So c ↦ γ_c is a homomorphism H → Ω. Checked.
- **Step 3, formula (GP1).** γ_cρ_aγ_c^{-1} = ρ_{cγ_c(a)c^{-1}}, checked on x, y and H. The
  element cγ_c(a)c^{-1} lies in H∗⟨y⟩, because γ_c preserves H∗⟨y⟩. Both special cases are
  correct:
  - k ∈ K commutes with C;
  - y l y^{-1} maps to y (c l c^{-1}) y^{-1}.
- **Step 4.** Φ is well defined on X = L ⋊ C, since the semidirect relation is exactly case 2 of
  (GP1). It is well defined on C × K by case 1. It agrees on C, so it extends to the amalgam.
  - In the common-retract route, the relation is checked on generators of L∗M. That suffices
    because both sides are homomorphisms of n.
- **Step 5.**
  - R: G → C glues the two retractions, so G = N ⋊ C with N = ⟨K, L⟩.
  - N ≅ K ∗ L by the amalgam normal form, because K ∩ C = 1 = L ∩ C.
  - w is injective: its image alternates between H∖1 and ⟨y⟩∖1.
  - Finally, Φ(nc) = id forces c^{-1}yc = y in H∗F, so c = 1, and then w(n) = 1.
  - Checked. Injectivity uses only that the letters are nontrivial in H; it needs no relation
    between K and L inside H.
- **Step 6.** For graph products, G_Γ = G_{Γ∖v} ∗_{G_{lk v}} (G_{lk v} × G_v), and G_{lk v} is a
  retract of G_{Γ∖v}. Induction on the number of vertices gives the result. Checked.
  - The trees-of-groups and equivariant parts of the common-retract node also check. The
    equivariant star is (G_{lk} × G_v) ⋊ C, which is the fibre product over C inside
    (G_{lk} ⋊ C) × (G_v ⋊ C).

## 3. Priority search (bounded)

- **Search 1.** arXiv API query for all:"Boone-Higman", sorted by date. The newest result is
  2609.01868 (2026-09-01, self-similarity of permutational wreath products). No abstract mentions
  graph products or Question 3.1.
- **Search 2.** arXiv API query for abs:"graph product" AND abs:simple since 2025-03. Nothing
  concerns embeddings into finitely presented simple groups.
- **Not searched:** MathSciNet and Google Scholar.
- **Status.** Within this search, Question 3.1 has no published answer. Main's affirmative
  answer rests on internal proofs plus BFFHZ Theorems C and E and Zaremsky Proposition 5.5.

## 4. Consequence

Every graph product over a finite graph whose vertex groups satisfy PBH also satisfies PBH, so
in particular it embeds in a finitely presented simple group. This answers BFFHZ Question 3.1
affirmatively, modulo the three imports. The common-retract generalization also holds.
