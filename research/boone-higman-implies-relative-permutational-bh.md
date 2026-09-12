---
rg: 2
id: boone-higman-implies-relative-permutational-bh
kind: claim
title: A group satisfying Boone--Higman sharply embeds in a type [A_2] actor modulo its action kernel
distinct_from:
  permutational-boone-higman-conjecture: that asks for an embedding in a finitely presented group with a FAITHFUL type (A) action; this is the relative form, where the action may have a kernel that the embedded group meets trivially, and whether it implies the faithful form is FFWZ Question 5.9.
  abstract-btb-simple-quotient-fp-gate: that says the simple quotient of a finitely presented abstract twisted Brin--Thompson group is finitely presented exactly when the action image is; this is the theorem placing every Boone--Higman group inside such a relative actor in the first place.
  boone-higman-conjecture: that is the open embedding conjecture; this is a proved consequence of it for each group that satisfies it.
---

**ESTABLISHED (literature import).** Fournier-Facio--Wu--Zaremsky,
arXiv:2603.24687v2, Theorem C (Theorem 5.1): "If a group satisfies the
Boone--Higman conjecture then it satisfies the relative permutational
Boone--Higman conjecture."

Their definitions, read through a summarizing fetch:
- **Normal pairs** (Definition 1.6). A normal pair (G,N) embeds in (G′,N′) if
  some injective ι: G → G′ has ι(G) ∩ N′ = ι(N). A group Γ *sharply embeds* in
  (G,N) when (Γ,{1}) embeds in (G,N).
- **Relatively simple** (Definition 1.2). A proper normal pair (G,N) is
  relatively simple if every proper normal subgroup of G lies in N.
- **relPBH** (Conjecture 1.8). For Γ finitely generated with solvable word
  problem, there is a group G with a type [A_2] action on a set S such that Γ
  sharply embeds in (G, ker(G↷S)).
- **Type [A_2].** G finitely presented, point stabilizers finitely generated,
  finitely many orbits on S^2. The action need not be faithful.

**Consequence for this graph.** Theorem C, with FFWZ Theorem A (abstract SV_G is
relatively simple) and Corollary 4.2 (`abstract-btb-simple-quotient-fp-gate`),
reduces the gap between Boone--Higman and its permutational form to one
question: can the action kernel be removed while keeping finite presentation?
That is FFWZ Question 5.9, "whether (relPBH)⇒(PBH)", and for this graph it is
`permutational-boone-higman-conjecture`.

DERIVATION
bh-implies-relative-pbh-citation
