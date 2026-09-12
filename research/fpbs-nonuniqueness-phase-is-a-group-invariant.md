---
rg: 2
id: fpbs-nonuniqueness-phase-is-a-group-invariant
kind: claim
title: If one Cayley graph of a group has a nonuniqueness phase then every Cayley graph does
distinct_from:
  fpbs-benjamini-schramm-universal: that asserts a nonuniqueness phase on every Cayley graph of every nonamenable group; this asserts only that the property does not depend on the generating set, and it is vacuous for a group none of whose Cayley graphs has the phase.
artifacts:
  - research/artifacts/fpbs/docs/benjamini-schramm-frontier-map.md
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
