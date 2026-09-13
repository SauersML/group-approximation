---
rg: 2
id: relative-automorphism-of-fp-simple-mif-group-has-type-a-action
kind: claim
title: For a finitely presented simple MIF group G and n at least 2, Aut_G(G * F_n) admits an action of type (A)
distinct_from:
  relative-automorphism-action-is-highly-transitive: that imports BFFHZ Propositions 2.3 and 2.6, high transitivity and finitely generated stabilizers for any infinite finitely generated simple base, with faithfulness left out; this imports their Theorem E, the full type (A) conclusion for a finitely presented simple MIF base, faithfulness included.
  fp-simple-highly-transitive-groups-satisfy-pbh: that is BFFHZ Theorem C, the characterization of the permutational class; this is Theorem E, the actor that Theorem C's proof of (iv) to (i) runs through.
artifacts:
  - research/artifacts/bh-type-a-actions-2026-09-12.md
---

**ESTABLISHED (literature import)** through
`relative-automorphism-mif-type-a-citation`.

> **Theorem E (Belk--Fournier-Facio--Hyde--Zaremsky, arXiv:2503.21882v2).**
> "For any finitely presented simple MIF group G, the group Aut_G(G ∗ F_n)
> (n ≥ 2) admits an action of type (A), and hence satisfies the (permutational)
> Boone–Higman conjecture."

Read from the extracted PDF text on MSI (`bh-reviewer/2503.21882.txt`,
l.195--198). The action is precomposition on `Hom_G(G * F_n, G)`.

**Their definition of type (A)** (l.120--126): "Given a group Γ acting
faithfully on a set S, we say that the action is of type (A) if: (i) The group Γ
is finitely presented. (ii) The stabilizer Stab_Γ(s) is finitely generated for
all s ∈ S. (iii) The action has finitely many orbits of pairs, i.e., the diagonal
action of Γ on S×S has finitely many orbits."

**Their proof** (l.640--647): faithfulness by their Lemma 2.2 (this is where MIF
is used), finite presentation by Proposition 1.1, finitely generated stabilizers
by Proposition 2.6 and transitivity (Lemma 2.1), and finitely many orbits of pairs
by Proposition 2.3. The internal propositions were not re-derived here.
