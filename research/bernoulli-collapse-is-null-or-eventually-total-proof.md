---
rg: 2
id: bernoulli-collapse-is-null-or-eventually-total-proof
kind: route
title: Code Bernoulli measures continuously, see isomorphism as a projection of Borel joinings, and apply Steinhaus to classes and own-square sets
target: bernoulli-collapse-is-null-or-eventually-total
requires:
  - bernoulli-isomorphism-collapse-set-is-a-subgroup
  - bernoulli-shifts-with-equal-base-entropy-are-isomorphic
artifacts:
  - research/artifacts/bernoulli-collapse-null-or-eventually-total-2026-09-16.md
---

"Item n" refers to the first prerequisite. The second prerequisite makes `X_h` well defined. "Section n" refers to
the artifact.

**Descriptive set theory used.** The following are standard (Kechris, *Classical Descriptive Set Theory*,
Sections 9, 14, 21 and 29; theorem numbers unverified):
- continuous images and Borel preimages of analytic sets are analytic;
- analytic sets are universally measurable and have the Baire property;
- Steinhaus and Pettis–Piccard: a subset of `R` that has positive measure, or has the Baire property and is
  non-meager, has a difference set containing `(−δ, δ)`.

**Item 1 (Section 1).**
- Geometric laws `γ_m` on `N ∪ {∞}` have entropy `φ(m) = (m+1)log(m+1) − m log m`, an increasing homeomorphism of
  `(0, ∞)`. So `h ↦ λ_h^G`, with `λ_h = γ_(φ^-1(h))`, is a continuous map `(0, ∞) → Prob((N ∪ {∞})^G)`.
- Isomorphism of shift-invariant measures on this compact zero-dimensional space is the projection of the Borel
  set of invariant couplings whose two coordinate σ-algebras agree mod null sets. That condition is `G_δ` on
  clopen sets. The coupling yields the isomorphism by a Lusin–Souslin argument.
- So `~` is analytic, and so are its sections, `D(G)`, `S(G)` and `R(G)`.

**Item 2 (Section 2).**
- **From `D(G)` to a class.** A positive `d ∈ D(G)` has `n ~ n + d` for all large integers `n` (Item 1). So
  `D(G) ∩ (0, ∞)` is a countable union of the sets `(C_n − n) ∩ (0, ∞)`. A non-null or non-meager `D(G)` gives a
  non-null or non-meager class.
- **From a class to eventual collapse.** Let `A = C_a ∩ (0, n]` be non-null or non-meager. Steinhaus or Pettis
  gives `δ`. For `e < δ`, pick `b_1 ~ b_2` in `A` with `b_2 − b_1 = e`. Translation by `z − b_1` (Item 1) gives
  `z ~ z + e` for all `z ≥ n`. Chaining small steps gives `[n, ∞)` inside one class.
- **Own-square levels.** For `b ∈ S(G)` and `u ≥ b`, translating `b ~ 2b` gives `u ~ u + b`. Two own-square levels
  `b_1 < b_2 ≤ n` give `u + b_1 ~ u + b_2` for `u ≥ n`. So a non-null or non-meager `S(G)` gives eventual collapse
  the same way.
- **The remaining implications.** They are trivial, or they are Fubini for the analytic set `~`.

**Item 3 (Section 3).**
- `R(G)` is upward closed by Item 1, and contained in `[s, ∞)` by the threshold in Item 6.
- A non-rigid `a` has an unbounded class, by an arithmetic progression from Item 1. Under eventual collapse this
  class meets `[M, ∞)`, so all non-rigid levels form one class.

**Item 4 (Section 4).**
- (T1) ⇒ (T4) because `s < h < 2h`.
- (T4) ⇒ (T3) is trivial.
- (T3) ⇒ (T2):
  - a non-null or non-meager `S(G)` gives `D(G) = R` by item 2;
  - an own-square level `h < a` gives `a ~ a + h`, so every `a > s` is non-rigid, and `r(G) ≤ s`;
  - `r(G) ≥ s` by item 3.
- (T2) ⇒ (T1) because the single class `R(G)` contains `(s, ∞)`.

**Item 5 (Section 5).** The relation "`b − a ∈ Γ`" is an equivalence relation, it is closed under translation,
and it contains the seeds. So it contains everything generated from them. Its classes are countable and it is
planar-null, so by item 2 it forces neither eventual collapse nor (T1).
