---
rg: 2
id: repetitive-amenable-schreier-counting-proof
kind: route
title: Count restrictions of the restricted image on Følner sets of the coset space, with disjoint transported certificates
target: repetitive-amenable-schreier-fixed-configurations-lie-in-image
requires:
  - injective-automata-restrict-to-schreier-graph-automata
artifacts:
  - research/artifacts/subgroup-fixed-configuration-transfer-2026-09-12.md
---

Section 2 of the artifact.

- **Setup.** Restrict to the graph automaton `tau_S` on `S = H\G`. If it is not onto, its closed image
  misses a pattern `p` on a finite `W`. That missing property is certified by the labelled ball
  `B_R(v_0)` containing `W.M`.
- **Upper bound.** Positive-density recurrence gives `c |Φ_k|` disjoint transported copies of the
  certificate inside `Φ_k`. So the restricted image has at most `q^|Φ_k| (1 - q^(-|W|))^(c |Φ_k|)`
  patterns on `Φ_k`.
- **Lower bound.** The decoder reads `v.N`, so those patterns determine the input on
  `Φ_k \ ∂_1 Φ_k`. That gives at least `q^(|Φ_k| - |∂_1 Φ_k|)` patterns.
- **Conclusion.** The two bounds contradict the Følner property. A finite coset space is the trivial
  case.
