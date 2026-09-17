---
rg: 2
id: fpbs-critical-volume-tail-gives-mean-field-susceptibility
kind: claim
title: A mean-field critical volume tail gives the mean-field susceptibility bound on every transitive graph
distinct_from:
  fpbs-triangle-condition-gives-mean-field-magnetization: that imports triangle condition implies critical volume tail n^(-1/2); this imports the next step, critical volume tail implies chi_p <= C/(p_c-p), which needs no triangle condition and holds on every transitive graph.
  fpbs-fibre-bubble-forces-mean-field-susceptibility: that derives the susceptibility bound over a hyperbolic quotient from a fibre bubble; this derives it on any transitive graph from the critical volume tail alone.
---

Published theorem, imported by citation. Let `G` be an infinite, connected,
locally finite, transitive graph, `K` the cluster of a fixed vertex and
`chi_p = E_p|K|`. If there is `C<infinity` with

    P_{p_c}(|K| >= n) <= C n^(-1/2)      for every n >= 1,

then there is `C''<infinity` with

    chi_p <= C''/(p_c - p)               for every 0 <= p < p_c.

This is item 2 of Hutchcroft's Theorem `thm:gammadelta_percolation`
(arXiv:1901.10363) with `delta=2` and `k=1`. It is the critical exponent
inequality `gamma <= delta - 1` at `delta = 2`. The bound uses neither
nonamenability nor the triangle condition.
