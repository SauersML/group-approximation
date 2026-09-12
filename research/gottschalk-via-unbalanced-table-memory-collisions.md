---
rg: 2
id: gottschalk-via-unbalanced-table-memory-collisions
kind: route
title: A strict automaton would give an unbalanced design whose minimal table group keeps its memory letters distinct
target: gottschalk-surjunctivity-conjecture
requires:
  - unbalanced-forward-tables-identify-memory-letters
  - strict-automata-give-injective-ca-with-skewed-site-marginals
  - strict-automata-live-on-canonical-table-groups
artifacts:
  - research/artifacts/unbalanced-design-memory-collisions-2026-09-12.md
---

Suppose `tau` on `A^G` is strict.
1. The second prerequisite gives an injective automaton on `(A^(k+1))^G` with a non-uniform one-site
   law, so its rule is unbalanced.
2. Its memory and a left-inverse memory, both finite subsets of `G`, give a design. The inclusion is a
   realization with a forward-sufficient table (Lemmas 1 and 4 of the canonical-table artifact).
3. A minimal forward-sufficient `E` below that table has a homomorphism `U_E -> G` sending each
   memory letter to its memory element (Lemma 5 there).
4. The memory elements are distinct in `G`, so the letters are distinct in `U_E`. This contradicts
   the first prerequisite.

This route forms an intended cycle with `unbalanced-table-memory-collisions-from-gottschalk`. The cycle
records an equivalence and establishes neither claim. Artifact, Theorem 3.
