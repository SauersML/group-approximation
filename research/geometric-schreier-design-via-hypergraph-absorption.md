---
rg: 2
id: geometric-schreier-design-via-hypergraph-absorption
kind: route
title: Quasirandom candidate graphs plus simultaneous matching by absorption
target: geometric-schreier-design
requires:
  - spherical-candidate-hypergraph-quasirandom
  - hypergraph-absorption-schreier-matching
---

The two-stage decomposition the design conjecture was built for: an analytic
stage that produces a combinatorial certificate, and a combinatorial stage
that consumes it.

Given the table and `eps`, fix the radius `r` and cloud size `N` supplied by
`spherical-candidate-hypergraph-quasirandom`, and sample the cloud.  With high
probability the coloured candidate hypergraph has almost uniform degrees,
controlled codegrees for distinct words, and the divisibility conditions —
none of the constants seeing the ambient dimension.  Feed that package to
`hypergraph-absorption-schreier-matching`, which returns one perfect matching
per generator whose composed word maps agree with the intended targets on
`1-o(1)` of the roots.  Those matchings are the labelled Schreier design.

The split is deliberate.  The first premise is a high-dimensional probability
estimate about caps on a sphere with a *fixed* unitary table; the second is a
theorem about coloured hypergraphs with no analysis in it.  Either can be
falsified on its own, and a failure of the first would kill the design
programme before any combinatorics is attempted.
