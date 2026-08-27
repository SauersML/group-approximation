---
rg: 2
id: star-identify-six-coset-charts-by-trace-saturation
kind: route
title: Identify five Weyl charts with one root chart by saturated projection traces
target: five-parahoric-overlap-saturations-give-global-shell-pvm
requires:
  - native-sl3-edge-parahoric-has-index-forty-two
---

Because `h_w` is Weyl-conjugate to `h`, it lies in the same `C` double
coset.  The stabilizer of the vertex `h_w C` is exactly `D_w`, so `(FOS1)`
is a well-defined bijection onto the common 42-vertex sphere.  This proves
the canonical correspondences `(FOS2)`.

For projections `P,Q`, normalized trace gives

```text
||P-Q||_2^2=tr(P)+tr(Q)-2tr(PQ).                        (FOS6)
```

Thus each `Delta_w` is a nonnegative scalar determined by pairwise trace
data, and summing `(FOS6)` over the five star edges gives `(FOS5)` exactly.
Zero deficit forces every corresponding pair of projections to be equal.

A graph connecting six chart vertices has at least five edges.  If the
comparison graph is disconnected, an independent unitary conjugation on
one component preserves all recorded projection traces inside every tested
edge while changing its placement relative to the other components.  Hence
connectedness is necessary, and the five-edge star is minimal.
