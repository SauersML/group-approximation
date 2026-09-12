---
rg: 2
id: fpbs-nonuniqueness-phase-is-a-group-invariant
kind: claim
title: If one Cayley graph of a group has a nonuniqueness phase then every Cayley graph does
distinct_from:
  fpbs-benjamini-schramm-universal: that asserts a nonuniqueness phase on every Cayley graph of every nonamenable group; this asserts only that the property does not depend on the generating set, and it is vacuous for a group none of whose Cayley graphs has the phase.
artifacts:
  - research/artifacts/fpbs/docs/benjamini-schramm-frontier-map.md
  - research/artifacts/fpbs-choi-seo-q12-invariance-2026-09-12.md
---

**OPEN.** Let `Gamma` be a finitely generated group. Suppose some finite
symmetric generating set `S`, not containing the identity, has
`p_c(Cay(Gamma,S)) < p_u(Cay(Gamma,S))`. Then every such generating set does.

This is Choi--Seo, arXiv:2508.08932v2, Question 1.2 (read from the PDF on
2026-09-12): "Is the existence of non-uniqueness phase a group-invariant?". They
add that an affirmative answer, together with Pak and Smirnova-Nagnibeda's
theorem, would settle the Benjamini--Schramm conjecture. That theorem is about
multigraph powers, so the existence input actually needed is
`fpbs-simple-generating-set-with-gap-exists`.

## Attempts

* **Class theorems are invariant by construction.** The hyperbolic, cost and
  acylindrically hyperbolic theorems prove the phase for all generating sets at
  once. They satisfy this claim on their classes without comparing two graphs.
  **Where it stops:** outside those classes, no argument compares percolation on
  two Cayley graphs of the same group.
* **Fibre-summed comparisons.** `fpbs-fibre-summed-connectivity-operator` and
  the RD weighted bubble criterion rewrite one graph's L2 condition as a
  positive kernel on a quotient. **Where it dies:** that kernel is built from the
  graph's own two-point function. It is not the two-point function of any other
  Cayley graph, so it compares nothing across generating sets.
* **Threshold comparison across generating sets (2026-09-12).**
  `fpbs-generating-set-threshold-comparison` does compare two Cayley graphs.
  - **Coupling.** Each edge of `G'` gets private randomness along a fixed word
    path in `G`, which gives `tau^{G'}_{phi(p)} <= tau^G_p` with
    `phi(p) = (1-(1-p)^{1/M})^L`.
  - **Consequences.** `p_u(G') >= phi(p_u(G))`, `p_c(G') >= phi(p_c(G))`, and
    for `S ⊆ S'` also `p_c(G') <= p_c(G)` and `p_u(G') <= p_u(G)`.
  - **Where it dies:** it transfers a gap only with a margin, roughly
    `p_c(G) < (p_u(G)/M)^L`. The power loss comes from buying independence
    along fixed paths.
* **Reduction to one move (2026-09-12).** By
  `fpbs-generating-sets-connected-by-product-moves`, any two generating sets are
  joined by moves that add or remove one product `uv` of two current generators.
  So this claim is equivalent to `fpbs-gap-survives-product-generator-moves`,
  wired through `fpbs-group-invariance-via-product-moves`. **Where it dies:** a
  counterexample needs a single move that pushes `p_u` down to `p_c`, inside the
  windows `phi(p_c(G)) <= p_c(G⁺) <= p_c(G)` and
  `phi(p_u(G)) <= p_u(G⁺) <= p_u(G)`. The comparison rules this out only when
  the windows are disjoint. Details are in
  `research/artifacts/fpbs-choi-seo-q12-invariance-2026-09-12.md`.
