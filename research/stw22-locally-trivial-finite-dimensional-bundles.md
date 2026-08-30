---
rg: 2
id: stw22-locally-trivial-finite-dimensional-bundles
kind: claim
title: Finite-dimensional locally trivial hyperfinite bundles have only uniform traces
distinct_from:
  stw22-finite-dimensional-trivial-field-traces: that theorem uses one global product chart; the present theorem allows arbitrary locally trivial Aut(R)-valued transition cocycles.
  stw22-finite-dimensional-colouring-from-local-lifts: that theorem assumes fixed global comparison corners; the present theorem proves that chartwise corners suffice because the colouring absorbs overlap between trivializations.
  stw22-tracefree-fibre-gap-ideals-force-trace-continuity: that is the abstract gap criterion; the present theorem verifies its hypothesis for a new class of nontrivial bundles.
artifacts:
  - research/artifacts/stw22-locally-trivial-bundle-audit-2026-08-30.md
---

Let `X` be compact metrizable with `dim(X)=d<infinity`, and let `M` be
the bounded continuous-section algebra of a locally trivial tracial
`W^*`-bundle over `X` whose fibre is the hyperfinite `II_1` factor `R`.
Here continuity is uniform `2`-norm continuity, and the local
trivializations have transition maps in `Aut(R)` with its pointwise
`2`-norm topology.  Then every norm/`2`-norm fibre gap

```text
K_x/J_x
```

has no nonzero bounded positive trace.  Consequently every tracial state
on `M` is uniquely

```text
a |-> integral_X tau_x(a(x)) dmu(x)
```

for a probability measure `mu` on `X`, and every trace is continuous for
the uniform `2`-norm.

No triviality of the `Aut(R)` cocycle is required.  The local replication
witnesses use independently chosen orthogonal corners in each product
chart.  A `(d+1)`-coloured refinement ensures that, at any base point and
for each colour, only one chart contributes.  Thus orthogonality is needed
only inside a single trivialization; contributions from different colours
cost the fixed factor `d+1`.  Transition automorphisms preserve the trace,
the purification equation, and orthogonality, so they create no additional
gluing term.
