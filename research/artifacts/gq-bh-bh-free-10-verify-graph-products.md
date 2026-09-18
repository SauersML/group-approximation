# Verification: permutational Boone–Higman is closed under graph products (BFFHZ Question 3.1)

Lane bh-free-10, 2026-09-18. This is an adversarial end-to-end check of
`pbh-class-closed-under-graph-products` and its route `pbh-graph-product-closure-proof`
(landed 2026-09-14, previously unreviewed). It is an internal verification, not an
external review.

**Verdict: PASS.** Every step checks. The only inputs are three literature results, and
all three were re-read at source:
- BFFHZ Theorem C (i) ⟹ (iv);
- BFFHZ Theorem E;
- Zaremsky's direct-product closure. BFFHZ use this themselves in their proof of
  Corollary F.

If the imports are as stated, the answer to BFFHZ Question 3.1 is **yes**.

## Sources re-read

arXiv:2503.21882v2 TeX source (`BHC_for_AutFn.tex`, 820 lines), fetched on MSI into
`gqsrc/bffhz/`:
- **l.206–215, Theorem C:** for a finitely generated G the following are equivalent:
  (i) PBH, (ii) f.p. twisted Brin–Thompson, (iii) f.p. simple highly transitive,
  (iv) f.p. simple MIF.
- **l.231–232, Theorem E:** for f.p. simple MIF G and n ≥ 2, Aut_G(G∗F_n) admits a
  type (A) action.
- **l.435:** proof of Theorem E. Faithfulness is the only place MIF is used.
- **l.443:** proof of Theorem C, via Zaremsky Theorem A, then high transitivity
  (BBMZ-hyp Prop. 5.4), then MIF (Hull–Osin Thm 5.9), then the embedding
  G ↪ Aut_G(G∗F_2).
- **l.447:** proof of Corollary F, free products (idea of X. Wu).
  - It uses Zaremsky Prop. 5.5 for A×B.
  - It then embeds A∗B in Aut_G(G∗F_n) by x_1 ↦ x_1 g and x_1 ↦ x_1(x_2^{-1} g x_2).
- **l.452–455, Question 3.1:** "Let G be a graph product over a finite graph such that
  each vertex group satisfies PBH. Does G satisfy PBH?"
- **l.457–458:** the authors note that general amalgams fail, because the word problem
  is tied to membership in the edge group.

The route is the natural extension of Wu's free-product argument. Transvections of one
letter realize the free factor K ∗ L. A new "twisted conjugation" γ_c (x ↦ xc,
y ↦ c^{-1}yc) realizes the retract C, acting compatibly on both factors.

## Step-by-step check

- **Step 0.**
  - K × X ∈ B_A by Zaremsky Prop 5.5, as BFFHZ use it at l.447, so K × X ≤ A with A an
    actor of type (A).
  - A is f.p. and f.g., and trivially satisfies (i). So (i) ⟹ (iv) gives A ≤ H with H
    f.p. simple MIF.
  - K and X commute in H and meet trivially. Correct.
- **Step 1.**
  - ρ_a (x ↦ xa, H and y fixed, a ∈ H∗⟨y⟩) is an automorphism with inverse ρ_{a^{-1}}.
  - ρ_aρ_b = ρ_{ab}, since b is fixed by ρ_a, and a ↦ ρ_a is injective. Correct.
- **Step 2.** γ_cγ_d = γ_{cd} on x and on y, and H is fixed. So c ↦ γ_c is a
  homomorphism H → Ω = Aut_H(H∗F(x,y)). Correct.
- **Step 3.** The formula γ_c ρ_a γ_c^{-1} = ρ_{c γ_c(a) c^{-1}} holds on x, on y and
  on H. This was recomputed:
  - on x: x ↦ xc^{-1} ↦ xac^{-1} ↦ xc·γ_c(a)·c^{-1};
  - on y: y ↦ cyc^{-1}, which ρ_a fixes, and then γ_c returns y.

  Both special cases are correct:
  - a = k ∈ K: C commutes with K, so the conjugate is ρ_k.
  - a = yly^{-1}: c·(c^{-1}yc)·l·(c^{-1}y^{-1}c)·c^{-1} = y(clc^{-1})y^{-1}.
- **Step 4.**
  - On X = L ⋊ C, the maps on L and on C are homomorphisms, and the conjugation
    relation is exactly the second case of Step 3.
  - On C × K, the two maps commute by the first case.
  - The two definitions agree on C, so Φ extends to X ∗_C (C × K) by the universal
    property. Correct.
- **Step 5.**
  - R is a retraction onto C, so G = N ⋊ C with N = ⟨K, L⟩.
  - N ≅ K ∗ L by the amalgam normal form, since K ∩ C = 1 = L ∩ C.
  - w: K ∗ L → H ∗ ⟨y⟩ (k ↦ k, l ↦ yly^{-1}) sends reduced words to reduced alternating
    words, so it is injective.
  - If ρ_{w(n)}γ_c = id, then evaluating at y gives c^{-1}yc = y, so c = 1, because a
    nontrivial element of the factor H does not commute with y. Then w(n) = 1, so
    n = 1. Correct.
- **Step 6.**
  - Induced subgraph groups are retracts.
  - G_Γ = G_{Γ∖v} ∗_{G_{lk v}} (G_{lk v} × G_v) is the standard decomposition.
  - Induction on the number of vertices is correct.

## Scope and hygiene

- **Coverage.** The vertex groups may be infinitely generated. B_A is closed under
  subgroups by definition, and the whole group sits inside Ω.
- **Consequences.**
  - The finitely presented simple envelope comes from Zaremsky Cor B, through
    `type-a-action-gives-boone-higman-for-subgroups`.
  - Solvable word problem holds for finitely generated G_Γ.
- **Novelty.** The cograph case (iterated free and direct products) was already known.
  The first new graph is P_4, as the node says.
- **Priority.**
  - On 2026-09-18, an arXiv API query for ("graph product" AND "Boone") returned 0
    entries.
  - Zaremsky's arXiv author listing shows no 2025–2026 paper on graph products.
  - No MathSciNet search was done. Default wording: no priority claimed.
- **Not re-derived.** BFFHZ's internal Propositions 1.1, 2.3 and 2.6 (f.p.,
  2-transitivity, f.g. stabilizers) are imported as the node states.
