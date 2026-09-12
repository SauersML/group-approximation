---
rg: 2
id: strict-automaton-bounds-rokhlin-supremum
kind: claim
title: A group carrying a strict injective automaton has an explicitly bounded Rokhlin entropy supremum
distinct_from:
  infinite-rokhlin-supremum-forces-surjunctivity: that is Seward's imported per-group implication from an infinite supremum; this gives an explicit finite upper bound on the supremum from one strict automaton, by a self-contained entropy code.
  bernoulli-entropy-counterexample-constraints: that bounds the supremum of a group where base entropy fails to classify Bernoulli shifts; this bounds it for a group where surjunctivity fails.
artifacts:
  - research/artifacts/gottschalk-rokhlin-entropy-route-2026-09-12.md
---

Let `G` be a countably infinite group, `|A| = q >= 2`, and `tau` an injective,
non-surjective cellular automaton on `A^G`. Let its image miss a pattern on the
finite window `Omega`. Put `delta = -log(1 - q^-|Omega|)`,
`D = |Omega Omega^-1|` and `k_0 = floor(D log 3/delta) + 1`. Then

    h^Rok_sup(G) < k_0 log q.

In Seward's labels INF(G) fails, and so does the equality of Bernoulli Rokhlin
entropy with base entropy at the base `A^(k_0)`. If `G` also contains a copy of
`G x G` and finite subgroups of unbounded order, as the binary Leavitt unit group
does, then `rokhlin-supremum-dichotomy-with-centralized-self-copies` forces
`h^Rok_sup(G) = 0`.

**ESTABLISHED 2026-09-12** by [[strict-automaton-bounds-rokhlin-supremum-proof]].
