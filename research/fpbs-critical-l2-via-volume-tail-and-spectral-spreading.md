---
rg: 2
id: fpbs-critical-l2-via-volume-tail-and-spectral-spreading
kind: route
title: Critical l2 from the universal mean-field volume tail and the universal vanishing normalized spectral radius
target: fpbs-nonamenability-bounds-critical-connectivity-operator
requires:
  - fpbs-critical-l2-iff-volume-tail-and-spectral-spreading
  - fpbs-critical-volume-tail-mean-field-universal
  - fpbs-normalized-two-point-spectral-radius-vanishes-universal
---

Decomposition route. Let `G` be a nonamenable transitive graph.

* `fpbs-critical-volume-tail-mean-field-universal` gives (V) on `G`.
* `fpbs-normalized-two-point-spectral-radius-vanishes-universal` gives (S) on
  `G`.
* Item 2 of `fpbs-critical-l2-iff-volume-tail-and-spectral-spreading` turns
  (V) and (S) into `||T_{p_c}||_(2->2) < infinity`.

The route is also necessary: item 2 shows each prerequisite holds on every
graph where the target holds. So it loses nothing, and a counterexample to
either prerequisite refutes the target. The two prerequisites are of
different kinds:

* (V) is a critical-exponent statement with no isoperimetric content;
* (S) is a subcritical spectral statement, and it fails on every amenable
  graph (item 5).

Through `fpbs-critical-l2-equivalent-to-dyadic-projection-estimate`, the same
pair decides the dyadic hole `fpbs-critical-dyadic-projection-estimate` on
nonamenable Cayley graphs (item 7).
