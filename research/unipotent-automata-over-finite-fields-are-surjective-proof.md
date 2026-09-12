---
rg: 2
id: unipotent-automata-over-finite-fields-are-surjective-proof
kind: route
title: Pull back to the formal polynomial ring and recover injectivity from the invertible linear part
target: unipotent-automata-over-finite-fields-are-surjective
requires: []
artifacts:
  - research/artifacts/low-degree-strict-pairs-linear-parts-2026-09-12.md
---

Direct proof, Section 7 of the artifact.

1. **Formal ring.** In `P = F[x_(u,i)]` over all `u in G`, with no reduction, automata act by
   ring endomorphisms, and `(psi phi)^* = phi^* psi^*`.
2. **Composites agree.** Every exponent of the formal composites `sigma tau` and `tau sigma`
   is at most `deg sigma * deg tau < q`. So these composites are reduced and equal the
   functional ones. `sigma tau = id` gives `tau^* sigma^* = id_P`, and `tau^*` is onto.
3. **Injectivity.** For `f != 0` with lowest homogeneous part `f_j`, the lowest part of
   `tau^*(f)` is `tau_A^*(f_j)`. It is nonzero because `tau_A` is a bijective linear automaton,
   so `tau_A^*` is a degree-preserving automorphism. Hence `tau^*` is injective.
4. **Conclusion.** `tau^*` is bijective, `sigma^* = (tau^*)^-1`, and `tau sigma = id` formally.
   By step 2 this holds as functions, so `tau` is onto.
