---
rg: 2
id: stw01-central-projection-ideal-extensions-preserve-qt-linearity
kind: claim
title: Central-projection ideal extensions preserve bounded quasitrace linearity
distinct_from:
  stw01-qt-invisible-ideal-extension-principle: that requires every bounded quasitrace on the ideal to vanish so the ambient quasitrace itself descends; here the ideal may carry nonzero traces, which are split off by central projections before a tail quasitrace descends.
  stw01-stable-ideal-extensions-force-qt-linearity: that verifies quasitrace invisibility using stability; a nonzero unital central corner is never stable, and the present theorem permits arbitrary nonzero traces on all such corners.
  stw01-directed-limits-preserve-qt-linearity: that approximates the entire algebra in norm by directed unital subalgebras; the central corners approximate only the ideal, while the complementary tail is controlled through the quotient.
  stw01-local-trace-rigid-models-force-linearity: that requires one trace-rigid subalgebra to approximate each ambient finite packet in norm; neither a proper ideal corner nor the quotient provides such an ambient approximation here.
artifacts:
  - research/artifacts/stw01-quasitrace-status-and-local-permanence-audit-2026-08-30.md
---

Let `A` be a unital C-star algebra and let `I triangleleft A` have an
increasing approximate unit of projections

```text
p_n in I intersect Z(A).
```

Suppose every bounded `2`-quasitrace on every nonzero unital ideal
`p_n A=p_n A p_n` is a trace, and every bounded `2`-quasitrace on `A/I` is a
trace.  Then every bounded `2`-quasitrace on `A` is a trace.

The ideal is not assumed quasitrace-invisible: each central corner may carry
arbitrary nonzero traces.  No exactness or separability assumption is used.

Exact centrality is the sharp algebraic hypothesis for the tail-compression
proof.  For a projection `p in A`, the cut

```text
a |-> (1-p)a(1-p)
```

is a star homomorphism onto `(1-p)A(1-p)` exactly when `p` is central.
With a merely quasicentral approximate unit the cuts are only asymptotically
multiplicative.  Composing a quasitrace with those completely positive cuts
does not, without further input, produce a quasitrace on `A/I`; in
particular approximate commutation cannot be replaced by the exact
commuting additivity axiom.  Thus the theorem does not claim the analogous
statement for arbitrary quasidiagonal extensions.
