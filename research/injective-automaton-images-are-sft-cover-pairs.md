---
rg: 2
id: injective-automaton-images-are-sft-cover-pairs
kind: claim
title: The image of an injective automaton over any group is a strongly irreducible SFT that contains every constant, and the inverse map makes it a bijective constant-point cover pair, so Gottschalk is exactly the bijective fragment of CP and sections are exactly SFT conjugacy subsystems
distinct_from:
  pointed-pre-injective-cover-pairs-admit-sections: that proves pointed injectivity gives a section and states the Gottschalk characterisation (its C3) with a domain that is only sofic, leaving the finite-type version open; this closes that gap, since the domain tau(A^G) is always a strongly irreducible SFT, and it sharpens Theorem Q from lift-closed prunings to SFT subsystems on which F is a conjugacy.
  strict-pairs-give-dual-failures-on-bounded-defect-domains: that builds the non-pre-injective pair (X_R, sigma) on a bounded-defect enlargement of tau(A^G) from a decoder; this uses tau(A^G) itself with the inverse tau^-1, needs no decoder, and gives a bijective pair.
  cover-pair-sections-force-fixed-point-surjectivity: that shows a section forces fixed-point surjectivity (D empty); this identifies the section's image as a strongly irreducible SFT through every constant on which F is bijective.
  constant-point-sft-domains-admit-no-post-surjective-covers: that is the open statement CP; this proves that its bijective fragment is equivalent to Gottschalk and isolates the rest as a colliding surplus.
artifacts:
  - research/artifacts/injective-image-sft-cover-pairs-2026-09-19.md
---

**ESTABLISHED (unreviewed)** by [[injective-automaton-images-are-sft-cover-pairs-proof]].
It is elementary, and part (a) is folklore: finite type is a conjugacy invariant. The new part is what it
gives in the cover-pair graph.

**Setting.** `G` is any group and `A` a finite alphabet. The action is `(g.x)(h) = x(g^-1 h)`. A *cover pair*
`(X, F)` is a closed subshift `X ⊆ A^G` with an automaton `F : X → A^G` that is strongly post-surjective with
lifts in `X` and constant `Φ`. That is, for `x ∈ X` and `z ~ F(x)` there is `x' ∈ X` with `F(x') = z` and
`Δ(x, x') ⊆ Δ(F(x), z)Φ`. It is *proper* if `X ≠ A^G`, and *constant-point* if `X` contains a constant.

**Theorem I.** Let `τ : A^G → A^G` be an injective cellular automaton with memory `S ∋ 1`, and let
`ν = τ^-1 : Y → A^G` on `Y = τ(A^G)`. Let `T ∋ 1` be a memory set of `ν`.
- (a) `Y` is the SFT of all `y` whose `K`-patterns, `K = ST`, all occur in `Y`.
- (b) `Y` is strongly irreducible.
- (c) `Y` contains every constant configuration. The constant map `a ↦ ν(a^G)` is a permutation of `A`, so the
  constant deficiency is `D = ∅`.
- (d) `(Y, ν)` is a cover pair with lift constant `Φ = S^-1`, and `ν` is a bijection `Y → A^G`.
- (e) `Y ≠ A^G` iff `τ` is not surjective.

**Theorem II (Gottschalk as a finite-type statement).** For a group `G` the following are equivalent.
1. `G` is not surjunctive.
2. Some proper constant-point SFT cover pair over `G` is injective on `Fin_c(X)` for some constant `c^G ∈ X`.
3. Some proper, strongly irreducible SFT cover pair over `G` contains every constant, has `D = ∅`, and has `F`
   bijective onto `A^G`.

**Theorem III (sections are SFT conjugacy subsystems).** A cover pair `(X, F)` has a section iff some subshift
`X' ⊆ X` is mapped bijectively onto `A^G` by `F`. When it does, `X' = s(A^G)` for a section `s`. `X'` is then a
strongly irreducible SFT through every constant, lift-closed with constant `M_s^-1`. This is Theorem Q of
`pointed-pre-injective-cover-pairs-admit-sections`, with "sofic pruning" replaced by "SFT conjugacy subsystem".

**Corollary (CP splits as Gottschalk plus a colliding surplus).** Write
- `CP_bij(G)`: no proper constant-point SFT cover pair has `F` bijective;
- `CP_col(G)`: no proper constant-point SFT cover pair collides on `Fin_c(X)` at every constant `c^G ∈ X`.

Then:

```text
CP_bij(G)  ⟺  Gottschalk(G),        CP(G)  ⟺  Gottschalk(G) ∧ CP_col(G).
```

- CP ⇒ Gottschalk now takes one line, through Theorem I, with no decoder and no bounded-defect domain.
- Either conjunct can fail on its own:
  - at a non-surjunctive group, the pair of Theorem I violates `CP_bij` and is not colliding;
  - in the monoid calibration of `cover-pair-sections-force-fixed-point-surjectivity`, `{a,b}*` is surjunctive
    but carries a pair that collides at its only constant. So the monoid analogue of `CP_col` fails while that of
    Gottschalk holds.

**What this does not do.** It does not decide CP, `CP_col` or `D ≠ ∅` at any nonsofic group. It does not bear on
the Leavitt-unit or Kun–Thom hosts beyond restating Gottschalk there.
