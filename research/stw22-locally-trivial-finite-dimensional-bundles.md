---
rg: 2
id: stw22-locally-trivial-finite-dimensional-bundles
kind: claim
title: Chartwise colouring recovers trace continuity for locally trivial hyperfinite bundles
distinct_from:
  stw22-finite-dimensional-trivial-field-traces: Evington--Pennig global triviality makes the present trace conclusion a formal special case of that theorem; the new content here is an independent chartwise proof which never chooses a global trivialization.
  stw22-finite-dimensional-colouring-from-local-lifts: that theorem assumes fixed global comparison corners; the present theorem proves that chartwise corners suffice because the colouring absorbs overlap between trivializations.
  stw22-tracefree-fibre-gap-ideals-force-trace-continuity: that is the abstract gap criterion; the present theorem gives a cocycle-local verification for locally trivial presentations of the already globally trivial bundle class.
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

This is **not** a new bundle class beyond
`stw22-finite-dimensional-trivial-field-traces`.  Evington--Pennig prove
that every locally trivial tracial `W^*`-bundle over a compact Hausdorff
base with all fibres isomorphic to `R` is globally trivial, with no
covering-dimension restriction.  Their theorem follows from contractibility
of `Aut(R)` in the relevant topology.  Hence the conclusion above is also
an immediate consequence of their global triviality theorem and the
existing finite-dimensional trivial-field result.

The independent content is the cocycle-local proof in
`stw22-colour-local-trivializations-proof`.  It does not first choose the
global gauge promised by Evington--Pennig.  Instead, local replication
witnesses use independently chosen orthogonal corners in each product
chart.  A `(d+1)`-coloured refinement ensures that, at any base point and
for each colour, only one chart contributes.  Thus orthogonality is needed
only inside a single trivialization; contributions from different colours
cost the fixed factor `d+1`.  Transition automorphisms preserve the trace,
the purification equation, and orthogonality, so they create no additional
gluing term.  This local technique may remain useful for bundle classes
whose structure group is not contractible.

The global triviality result is S. Evington and U. Pennig,
[*Locally Trivial W*-Bundles*](https://arxiv.org/abs/1601.05964),
Theorem 4.10.
