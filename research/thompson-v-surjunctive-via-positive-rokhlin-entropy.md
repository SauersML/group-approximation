---
rg: 2
id: thompson-v-surjunctive-via-positive-rokhlin-entropy
kind: route
title: Embed V x V and the cylinder permutation groups in V and apply the self-copy dichotomy
target: thompson-v-surjunctive
requires:
  - thompson-v-has-positive-rokhlin-entropy-action
  - rokhlin-supremum-dichotomy-with-centralized-self-copies
  - positive-rokhlin-entropy-action-gives-positive-supremum
  - infinite-rokhlin-supremum-forces-surjunctivity
artifacts:
  - research/artifacts/rokhlin-co-amenable-ascent-and-thompson-v-2026-09-12.md
  - research/artifacts/rokhlin-entropy-self-copy-dichotomy-2026-09-12.md
---

Section 3 of the artifact.

1. **Self-copies.** `V` acts on `{0,1}^N` by prefix replacement. For a word w, conjugating by `x -> wx` identifies `V` with `V_[w]`, the elements supported in `[w]`. `V_[0]` and `V_[1]` have disjoint supports, so they commute and meet trivially, and `V x V <= V`. Permuting the `2^n` cylinders of length n gives `Sym(2^n) <= V`, so `V` has finite subgroups of unbounded order. The reviewed Remark 2.5 of the dichotomy artifact records the same.
2. **Dichotomy.** Corollary A1 of `rokhlin-supremum-dichotomy-with-centralized-self-copies` gives `h^Rok_sup(V) ∈ {0, infinity}`.
3. **POS to INF.** A free ergodic action of positive Rokhlin entropy gives `h^Rok_sup(V) > 0` (`positive-rokhlin-entropy-action-gives-positive-supremum`), hence `h^Rok_sup(V) = infinity` by step 2.
4. **INF to surjunctivity.** `infinite-rokhlin-supremum-forces-surjunctivity` makes `V` surjunctive, and `K[V]` directly finite for every field `K`.

The first prerequisite is open, so this route establishes nothing yet.
