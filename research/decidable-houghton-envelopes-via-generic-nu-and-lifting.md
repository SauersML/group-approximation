---
rg: 2
id: decidable-houghton-envelopes-via-generic-nu-and-lifting
kind: route
title: Take a generic enumeration so the near shift group is P*Z, read off a finitely presented germ group for H_3(E_nu(P)), and lift
target: decidable-inputs-have-fp-houghton-like-shift-envelopes
requires:
  - regular-enumerations-can-make-near-shift-free-product
  - houghton-like-envelopes-have-fp-germs-iff-fp-near-shift-group
  - houghton-like-envelopes-lift-finite-presentation-from-germs
  - mallery-zaremsky-shift-similar-envelope
  - half-finite-generators-with-e2-are-strongly-shift-similar
  - houghton-like-groups-are-strongly-shift-similar
---

**DEAD (bh-map, 2026-09-18).** Step 4 requires `houghton-like-envelopes-lift-finite-presentation-from-germs`, which is refuted. Its conclusion is also false for the enumerations of step 1: by `free-shift-houghton-like-envelopes-are-not-fp`, `H_3(E_nu(P))` is not finitely presented when `R_nu = P*<s>`. Kept as a record of the attempt.

Let `P` be an infinite finitely presented group with solvable word problem.

1. By `regular-enumerations-can-make-near-shift-free-product`, choose `nu` (computably, from the word-problem
   algorithm) with `R_nu = <lambda(P), s> ≅ P * <s>`. This group is finitely presented because `P` is.
2. `G := E_nu(P)` is finitely generated and strongly shift-similar (`mallery-zaremsky-shift-similar-envelope`,
   `half-finite-generators-with-e2-are-strongly-shift-similar`).
3. By `houghton-like-envelopes-have-fp-germs-iff-fp-near-shift-group` item 3, with `n = 3`, the germ group
   `H_3(G)/FSym([3] x N)` is finitely presented.
4. By `houghton-like-envelopes-lift-finite-presentation-from-germs` (OPEN) with `n = 3`, `H_3(G)` is finitely
   presented. ∎

Only step 4 is open. Steps 1–3 are established, and they hold for every infinite finitely presented `P`. Solvable
word problem is used only to make `nu` computable; the route does not need that.
