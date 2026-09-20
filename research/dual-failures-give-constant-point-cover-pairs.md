---
rg: 2
id: dual-failures-give-constant-point-cover-pairs
kind: claim
title: A post-surjective automaton that is not pre-injective restricts to a cover pair on a one-pattern SFT through every constant, so CP implies dual surjunctivity group by group
distinct_from:
  alphabet-enlarging-covers-refute-dual-and-domain-duality: that turns an alphabet-enlarging cover (an NPE failure) into failures of dual surjunctivity, CP and PSD, all deficient; this turns any dual failure, over the same alphabet, into a CP failure whose domain contains every constant, and it gives CP ⇒ dual surjunctivity, not only CP ⇒ NPE.
  constant-point-sft-domains-admit-no-post-surjective-covers: that is the open non-existence statement CP; this proves that a dual failure at a group refutes it there.
  every-group-is-dual-surjunctive: that is the open statement that dual failures do not exist; this shows each one yields a CP counterexample.
  surjunctive-groups-are-dual-surjunctive: that is the open implication Gottschalk ⇒ dual surjunctivity; this shows every proof of Gottschalk ⇒ CP at a group proves it at that group.
  pointed-pre-injective-cover-pairs-admit-sections: that converts pointed-injective cover pairs into sections, i.e. into Gottschalk failures; this converts non-pre-injective full-shift automata into cover pairs, i.e. into CP failures.
  strict-pairs-give-dual-failures-on-bounded-defect-domains: that builds dual failures on bounded-defect domains from strict pairs; this goes the other way, from a dual failure on the full shift to a cover pair on a proper domain.
artifacts:
  - research/artifacts/erasable-pattern-avoiding-cover-pairs-2026-09-19.md
  - experiments/erasable-pattern-avoidance-2026-09-19/check_unbordered_context.py
---

**ESTABLISHED 2026-09-19** by [[dual-failures-give-constant-point-cover-pairs-proof]]. Elementary, modulo the
imported Doucha–Gismatullin equivalence of post-surjectivity and strong post-surjectivity.

**Statement.** Let `G` be a group, `A` a finite alphabet, and `F : A^G → A^G` a post-surjective automaton that is
not pre-injective, i.e. a counterexample to `every-group-is-dual-surjunctive` at `G`. Then there is a
non-constant pattern `w'` on a finite `L' ⊆ G` such that:
1. `X = {x : w' occurs nowhere in x}` is a proper SFT of `A^G` that contains every constant configuration;
2. `F|_X : X → A^G` is strongly post-surjective with lifts in `X`, in the sense of
   `strict-pairs-give-dual-failures-on-bounded-defect-domains`.

So `(X, F|_X)` refutes `constant-point-sft-domains-admit-no-post-surjective-covers` (CP) at `G`, with the same
alphabet on both sides.

**Consequences.**
- `CP(G) ⇒ DualSurj(G)` for each group `G`, and CP over all groups ⇒ `every-group-is-dual-surjunctive`. This
  strengthens `CP ⇒ NPE` from `alphabet-enlarging-covers-refute-dual-and-domain-duality`. With `CP ⇒ Gottschalk`,
  CP is a common strengthening of Gottschalk and of dual surjunctivity.
- Over a surjunctive `G` the pair collides on the class of every constant, by
  `pointed-pre-injective-cover-pairs-admit-sections`. So `Gottschalk(G) ∧ ¬DualSurj(G) ⇒ ¬CP_col(G)`.
- **Obstruction.** Any proof of `Gottschalk(G) ⇒ CP(G)`, which is what needs 36774ad3 and 06d50d0e ask for via `CP_col`,
  proves `surjunctive-groups-are-dual-surjunctive` at `G`, and that claim is OPEN.
- The pair need not be deficient (every constant lies in `X`), so it escapes the deficiency class kill of
  `cover-pair-sections-force-fixed-point-surjectivity`.

**Idea.**
1. Two asymptotic points with the same image give patterns `u ≠ u'` on a finite window `L` that differ on
   `K ⊆ L`. Switching `u ↔ u'` on `gK` at any occurrence preserves `F`, whatever the context.
2. A random context `c` on a large window `L' ⊇ L` (a word ball in an infinite finitely generated subgroup, or a
   large finite subgroup when `G` is locally finite) makes `w' = u' ∪ c` unbordered against `w = u ∪ c`. Swapping
   one occurrence of `w'` into `w` then creates no new occurrence.
3. Lift in `A^G`, and swap out the finitely many new occurrences of `w'` one at a time.
