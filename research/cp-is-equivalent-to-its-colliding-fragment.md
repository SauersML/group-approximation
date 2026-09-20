---
rg: 2
id: cp-is-equivalent-to-its-colliding-fragment
kind: claim
title: The bounded-defect route pair collides at every constant, so CP is equivalent to its colliding fragment CP_col, CP_col alone implies Gottschalk, and the real surplus of CP over Gottschalk is the sectionless fragment
distinct_from:
  injective-automaton-images-are-sft-cover-pairs: that splits CP as Gottschalk ∧ CP_col and says CP_col is a surplus the route never uses; this shows the route pair (X_R, σ) itself refutes CP_col at every non-surjunctive group, so CP_col ⇒ Gottschalk, the split is redundant, and the surplus is the sectionless fragment instead.
  strict-pairs-give-dual-failures-on-bounded-defect-domains: that proves (X_R, σ) is not pre-injective, at one unspecified asymptotic class; this reads its proof at every constant and records what that does to the CP split.
  pointed-pre-injective-cover-pairs-admit-sections: that shows sectionless pairs collide at every constant; this adds that sectioned pairs (the route pairs) collide at every constant too, so collisions do not separate the two.
  constant-point-sft-domains-admit-no-post-surjective-covers: that is CP itself; this is an equivalence between CP and one of its fragments, and it decides nothing at any nonsofic group.
artifacts:
  - research/artifacts/bounded-defect-domain-duality-2026-09-17.md
  - research/artifacts/injective-image-sft-cover-pairs-2026-09-19.md
---

**ESTABLISHED (unreviewed)** by [[cp-is-equivalent-to-its-colliding-fragment-proof]]. Elementary. It reads
item 4 of `bounded-defect-domain-dual-failure-proof` at a constant base point.

**Setting.** As in `injective-automaton-images-are-sft-cover-pairs`. A *cover pair* `(X, F)` is a closed
subshift `X ⊆ A^G` and an automaton `F : X → A^G` that is strongly post-surjective with lifts in `X`. It is
*proper* if `X ≠ A^G` and *constant-point* if `X` contains a constant. It *collides at* `c^G ∈ X` if `F` is not
injective on `Fin_c(X) = {x ∈ X : x ~ c^G}`. Write
- `CP(G)`: no proper constant-point SFT cover pair exists over `G`;
- `CP_col(G)`: no proper constant-point SFT cover pair over `G` collides at every one of its constants;
- `CP_col^∃(G)`: no proper constant-point SFT cover pair over `G` collides at some constant;
- `CP_nosec(G)`: no proper constant-point SFT cover pair over `G` lacks a section.

**Theorem.** Let `G` be a non-surjunctive group with strict pair `(τ, σ)` on `A^G`. Take `W`, `R` as in the
Assembly of `bounded-defect-domain-dual-failure-proof`. Then `(X_R, σ|_{X_R})` is a proper, strongly
irreducible SFT cover pair that
1. contains every constant configuration;
2. has constant deficiency `D = ∅` and a section, namely `τ`;
3. collides at every constant `c^G`.

**Corollary 1 (the split collapses).** For every group `G`,

```text
CP(G)  ⟺  CP_col(G)  ⟺  CP_col^∃(G),      and  CP_col(G) ⇒ Gottschalk(G).
```

The corollary of `injective-automaton-images-are-sft-cover-pairs` says `CP ⟺ Gottschalk ∧ CP_col`. Its
conjunct `Gottschalk` is redundant. Its remark that "either conjunct can fail on its own" is false over groups:
Gottschalk cannot fail while `CP_col` holds. The remark is true only for the free monoid, which is not a group.
Its line "CP adds only CP_col, which the route never uses" is also wrong: the route pair of
`gottschalk-via-constant-point-domains` is a `CP_col` pair.

**Corollary 2 (the correct surplus).** `CP(G) ⟺ Gottschalk(G) ∧ CP_nosec(G)`. Here:
- the sectioned fragment is Gottschalk (Proposition C of the scheduled-sections artifact);
- every sectionless pair collides at every constant (Theorem P of
  `pointed-pre-injective-cover-pairs-admit-sections`);
- at a surjunctive `G`, `CP_nosec(G) = CP(G)`.

So collisions do not separate the Gottschalk witnesses from the surplus: sectioned and sectionless pairs both
collide everywhere. The only separating invariant is whether a section exists.

**Class kill (collision-profile restrictions).** Take any restriction of CP to a class of pairs defined by
profile data. Profile data is any conjunction of: strong irreducibility, `D = ∅`, containing every constant,
colliding at every constant, non-pre-injectivity, `Φ` and window sizes above a bound. Every such restriction
still implies Gottschalk, since the route pair `(X_R, σ)` has every one of these properties.
- Invariant: the collision/deficiency/irreducibility profile of a pair.
- Dying step: the Theorem, items 1–3. The route pair realises the most degenerate profile.
- Consequence: an argument that refutes a pair from its profile alone (Garden-of-Eden-type counting of collisions
  against lifts, entropy drop from collisions, deficiency arguments) proves Gottschalk on the way. It is not a
  reduction of CP to something weaker than Gottschalk. The only restrictions of CP strictly weaker than CP that
  stay on the route must mention sections, or data equivalent to them (Theorem III of
  `injective-automaton-images-are-sft-cover-pairs`).

**With the bus.** Combined with swarm-0917-w19's Theorem D (bus lemma, not yet landed here: post-surjective
non-pre-injective automata on `A^G` restrict to CP counterexamples), this gives `CP_col(G) ⇒ DualSurj(G)`. With
`cover-pair-failures-have-finite-partial-table-witnesses`, it gives `CP(all groups) ⟺ CP_col(U)` for the fixed
tester `U`, with no `Gottschalk(U)` conjunct.

**What this does not do.** It decides CP, `CP_col` and `CP_nosec` at no nonsofic group. It does not touch needs
36774ad3 or 06d50d0e.
