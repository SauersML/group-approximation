---
rg: 2
id: brown-mcduff-witness-for-simple-kazhdan-lef-group
kind: claim
title: The simple Kazhdan LEF subshift group lies in the unitary group of a separable R^omega-embeddable McDuff factor, and admits no faithful representation into U(R)
distinct_from:
  simple-kazhdan-group-gives-property-t-factor-in-r-omega: that records the property (T) factor L(G_X) inside R^omega; this gives the separable McDuff factor that Brown's question literally asks for, and shows that the hyperfinite factor cannot serve.
  infinite-simple-kazhdan-hyperlinear-group: that is the existence question in its hyperlinear form; this is the bridge to Brown's von Neumann form for one explicit group.
artifacts:
  - research/artifacts/sk-operator-algebras-proposal-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `X` be an infinite minimal subshift and `S = EL_3(LC(X,F_q) ⋊ Z)/Z` (for `q = 2` the
centre is trivial and `S = G_X` of the note).
- **(a)** `s ↦ λ_s ⊗ 1` embeds `S` in the unitary group of `M = L(S) ⊗̄ R`, a separable McDuff II_1 factor that embeds in `R^ω`.
- **(b)** There is no injective homomorphism `S → U(R)`, where `R` is the hyperfinite II_1 factor.

So `S` answers Brown's question as printed (arXiv:math/0111286v1, §11, Question 7):
> Can an infinite, simple, discrete group with Kazdan's property T be embed into the unitary group of an
> R^ω-embeddable McDuff factor? (Compare with [robertson] where it is shown that no such embedding exists into the
> unitary group of L(F_n) ⊗̄ R or, more generally, L(Γ) for any a-T-amenable discrete group Γ.)

By (b), the hyperfinite McDuff factor never works for such a group, so any witness is a non-hyperfinite McDuff factor.

Proof route: `brown-mcduff-witness-for-simple-kazhdan-lef-group-proof`. Sources are quoted verbatim in
`research/artifacts/sk-operator-algebras-proposal-2026-09-13.md` §1.
