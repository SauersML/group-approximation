---
rg: 2
id: fpbs-critical-volume-tail-mean-field-universal
kind: claim
title: Every nonamenable transitive graph has the mean-field critical volume tail
distinct_from:
  fpbs-triangle-condition-gives-mean-field-magnetization: that derives the volume tail from the triangle condition on a given graph; this asserts the tail on every nonamenable transitive graph, with no triangle hypothesis.
  fpbs-critical-volume-tail-gives-mean-field-susceptibility: that imports the implication from the tail to gamma=1; this is the OPEN universal statement of the tail itself.
  fpbs-nonamenability-bounds-critical-connectivity-operator: that is critical l2 boundedness, which implies this tail; this is the half of the l2 conjecture that is a critical exponent statement, and it is not known to imply l2.
---

OPEN. Let `G` be a connected, locally finite, transitive, nonamenable graph.
Then there is `C<infinity` with

    P_{p_c}(|K_o| >= n) <= C n^(-1/2)      for every n >= 1.

This is condition (V) of `fpbs-critical-l2-iff-volume-tail-and-spectral-spreading`.
There, critical l2 boundedness is shown to be equivalent to (V) together with
the spectral condition (S) of
`fpbs-normalized-two-point-spectral-radius-vanishes-universal`.

**How it can fail independently of (S).** (V) says only that the critical
exponent `delta` equals 2. It uses no isoperimetry, and it is expected to
fail on low-dimensional lattices, where `delta>2` is predicted. This
expectation is not imported. A nonamenable transitive
graph with `delta>2` would refute this node and the l2 conjecture together,
whatever (S) does.

## Attempts

* **2026-09-17, split from critical l2.** Recorded as one of the two
  independent halves of critical l2. The known classes with `p_c<p_(2->2)`
  (Gromov hyperbolic, nonunimodular, acylindrically hyperbolic, free products
  on union generating sets) satisfy (V) through the triangle condition. No
  argument is known for a general nonamenable graph.
