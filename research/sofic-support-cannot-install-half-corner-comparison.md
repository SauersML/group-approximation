---
rg: 2
id: sofic-support-cannot-install-half-corner-comparison
kind: claim
title: A half-corner chart comparison needs a nonsofic actor subgroup
distinct_from:
  non-nesting-transporters-cannot-install-chart-comparison: that kills single transporters whose two charts generate a finite block group, by a rank count on the block module; this kills every candidate Z whose support generates a sofic group together with the chart, at every support and coefficient choice, by a faithful rank function that is regular on the chart.
  chart-comparison-must-fuse-torus-classes: that constrains the finite images of the actor subgroup that are injective on the chart; this constrains the actor subgroup itself, including actor subgroups with no nontrivial finite images.
  subgroup-supported-one-sided-inverse-rigidity: that concerns a one-sided inverse of an element of a corner of a directly finite subgroup algebra; this concerns a split embedding between two different idempotents of equal regular rank, and consumes the faithful regular rank function of a sofic subgroup rather than direct finiteness alone.
  linear-sofic-group-algebra-is-stably-finite: that makes the support of a complete one-sided inverse pair non-linear-sofic; this is the sharper statement for the comparison stage, whose support can be small, and it needs a rank function regular on the chart, which linear sofic approximations do not provide.
artifacts:
  - research/artifacts/gottschalk-negative-side-verification-2026-09-12.md
---

**ESTABLISHED.** Let `k` be a field, `G` a group, `K <= G` a finite
subgroup, and `f, P in k[K]` idempotents of equal regular rank,
`dim_k f k[K] = dim_k P k[K]`, which are not Murray--von Neumann equivalent
in `k[G]`. If

```text
Z in P k[G] f,      L in f k[G] P,      L Z = f,
```

then the subgroup `H = <K, supp Z>` is not sofic.

## Application to the half-corner target

Take `Q = L_(F_2)(1,2)^x`, `S = F_2[Q]` and the chart `K ~= GL_2(F_4)` of
`half-corner-chart-comparison-exists`. The pair `(f_+, P)` (regular rank 40)
and the reduced pair `(f_0, P_0)` (regular rank 32) satisfy the hypotheses.
Evaluation `ev : S -> L_(F_2)(1,2)` gives `ev(f_+) = ev(f_0) = 0` and
`ev(P) = ev(P_0) = p_01 != 0`, and a Murray--von Neumann equivalence would
survive the ring map. So **every solution of the comparison, full or
reduced, has a nonsofic actor subgroup `<K, supp Z>`.**

* **What it kills.** Every actor family that generates a sofic group together
  with `K`, at every support of `Z` and `L` and every coefficient choice. This
  covers finite, locally finite, residually finite and amenable actor
  subgroups, and amenable extensions of these. `L` is never constrained: a
  conditional expectation moves it into `k[H]`.
  `non-nesting-transporters-cannot-install-chart-comparison` is the finite
  case.
* **What survives.** `Z` must generate, with `K`, a group outside every class
  known to be sofic. For a single Thompson transporter this is a necessary
  condition only, and the exact exterior screens remain the practical filter.
  Soficity of Thompson's group `V` is open, so transporter families inside
  `<K, V>` are not excluded as such.
* **Scope.** The rank function used is regular on `K`. A linear sofic
  approximation gives a faithful rank function whose restriction to `K` need
  not be regular: `f_+` and `P` already have ranks `0` and `2` on the natural
  module. So this argument says nothing about linear sofic actor subgroups at
  the comparison stage. A complete scalar witness, however, has
  non-linear-sofic support by `linear-sofic-group-algebra-is-stably-finite`.

Proof: [[sofic-support-half-corner-comparison-proof]].
