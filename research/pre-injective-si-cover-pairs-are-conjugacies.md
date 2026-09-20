---
rg: 2
id: pre-injective-si-cover-pairs-are-conjugacies
kind: claim
title: A pre-injective SFT cover pair splits as a product over the fibre of a constant, and on a strongly irreducible domain that fibre is one constant, so the cover is a conjugacy onto the full shift and the dual-failure claim is equivalent to the absence of proper SI SFT covers
distinct_from:
  pointed-pre-injective-cover-pairs-admit-sections: that assumes injectivity on the class of one constant already present in X and builds a section; this assumes injectivity on every class and no constant, and proves that on SI domains the constant exists and F is a conjugacy.
  proper-sft-domains-admit-no-dual-failures: that is the target statement, asking that proper SI SFT cover pairs be pre-injective; this proves that a pre-injective one is a conjugacy, so that claim is equivalent to there being no proper SI SFT cover pair at all.
  injective-automaton-images-are-sft-cover-pairs: that shows the image of an injective automaton is a bijective cover pair; this is the converse on SI domains, where every pre-injective cover pair is bijective and so comes from such an image.
  constant-point-sft-domains-admit-no-post-surjective-covers: that forbids covers on constant-point SFT domains; this is about strongly irreducible domains with no constant assumed, and its pre-injective case recovers the bijective fragment of that claim's split.
artifacts:
  - research/artifacts/pre-injective-cover-pair-products-2026-09-20.md
---

**ESTABLISHED (unreviewed)** by [[pre-injective-si-cover-pairs-are-conjugacies-proof]]. Elementary.

**Setting.** `A` is a finite alphabet, `G` a group, `(g.x)(h) = x(g^-1 h)`. A *cover pair* `(X, F)` is an SFT
`X ⊆ A^G` with an automaton `F : X → A^G` that is strongly post-surjective with lifts in `X` with constant `Φ`:
for `x ∈ X` and `z ~ F(x)` there is `x' ∈ X`, `x' ~ x`, `F(x') = z`, `Δ(x, x') ⊆ Δ(F(x), z)Φ`. This is the
definition of `strict-pairs-give-dual-failures-on-bounded-defect-domains`. `F` is *pre-injective* if distinct
asymptotic points of `X` have distinct images.

**Theorem S (product splitting).** Let `(X, F)` be a pre-injective cover pair, let `d ∈ A`, and put
`Z = X ∩ F^-1(d^G)`.
1. *Transport.* There is an automaton `S : X × A^G → X` with `F(S(x, y)) = y`, `S(x, F(x)) = x` and
   `S(S(x, y), z) = S(x, z)`. For `y ~ F(x)`, `S(x, y)` is the unique `x' ~ x` with `F(x') = y`.
2. *Splitting.* `x ↦ (S(x, d^G), F(x))` is a conjugacy `X → Z × A^G` with inverse `(z, y) ↦ S(z, y)`, and it
   carries `F` to `pr_2`. `Z` is a nonempty SFT, and no two distinct points of `Z` are asymptotic.

**Theorem C (SI domains).** If moreover `X` is strongly irreducible, then `Z = {c^G}` for a constant `c^G`, and
`F : X → A^G` is a conjugacy. If also `X ≠ A^G`, then `F^-1 : A^G → X ⊊ A^G` is injective and not surjective, so
`G` is not surjunctive.

For `X = A^G` this is the full-shift fact that pre-injective, post-surjective automata are reversible
(Capobianco–Kari–Taati). That paper is cited only for consistency and is not imported; the proof here is
self-contained.

**Corollaries (per group `G`).** Put `NoCover_SI(G)` for: no proper SI SFT `X ⊊ A^G`, over any alphabet, carries
a cover pair.
1. `Gottschalk(G)` holds iff no proper SI SFT cover pair over `G` is pre-injective. The reverse direction uses
   `injective-automaton-images-are-sft-cover-pairs`.
2. `proper-sft-domains-admit-no-dual-failures` at `G` is equivalent to `NoCover_SI(G)`. Its escape clause, "or
   `F` is pre-injective", is inert at every group. The forward direction uses `PSD ⇒ Gottschalk` from
   `strict-pairs-give-dual-failures-on-bounded-defect-domains`, together with Corollary 1.
3. So PSD at `G` is `Gottschalk(G)` together with `PSD_col(G)`: no proper SI SFT cover pair collides. The
   bijective fragment is exactly Gottschalk, just as in the split `CP ⟺ Gottschalk ∧ CP_col` of
   `constant-point-sft-domains-admit-no-post-surjective-covers`. Here the colliding part is the whole
   statement, since PSD already implies Gottschalk.

**Class kill (proving pre-injectivity).**
- *The approach.* Prove PSD, or its constant-point form, by deriving pre-injectivity from strong
  post-surjectivity on an SI domain. This is the dual-surjunctivity pattern, where post-surjective implies
  pre-injective, and it includes pruning and collision-removal schemes.
- *Invariant.* Pre-injectivity of a proper SI SFT cover pair.
- *Dying step.* This is Theorem C. Over a surjunctive group, no proper SI SFT cover pair is pre-injective. So
  "every such pair is pre-injective" holds there only vacuously, and a proof of it is a non-existence proof. A
  scheme that turns a given pair into a pre-injective one, by pruning collisions, passing to a subsystem or
  changing the cover, therefore manufactures a Gottschalk counterexample. It can succeed only at non-surjunctive
  groups. The non-existence route is the one taken by the amenable entropy sketch and by the sofic counting of
  `proper-sft-covers-exclude-finite-orbits-and-sofic-constants`.
- *Consequence.* Every correct attack on PSD is a non-existence proof for proper SI SFT covers. The
  "not pre-injective" hypothesis supplies nothing beyond `Gottschalk(G)`.
