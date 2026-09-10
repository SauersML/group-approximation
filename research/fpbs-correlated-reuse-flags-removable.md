---
rg: 2
id: fpbs-correlated-reuse-flags-removable
kind: claim
title: Group-correlated reuse flags can be removed without increasing completed cost
artifacts:
  - research/artifacts/fpbs/docs/relative-cycle-exchange.md
  - research/artifacts/fpbs/docs/fixed-price-reuse-localization.md
  - research/artifacts/fpbs/docs/fixed-price-reuse-compression.md
  - research/artifacts/fpbs/responses/55_0909-215618.md
---

**OPEN.** For a factor map pi from a free action Y onto a free action X of a finitely generated group, and in particular for the projection a x b -> b onto a Bernoulli action, prove that there are finite routing plans on Y with budget tending to C(Y) whose conditional traffic defect for pi tends to zero. Equivalently, prove that every free extension generated over its base by the orbit name of one binary observable preserves cost; equivalently, that the pushforwards of the unused-edge measures and of the repeated-use measures can be made asymptotically singular while the near-optimal edge budget is preserved.

This is the isolated remaining step of the reuse programme. The savings to be preserved are those of a connection used many times and paid for once, and the question is whether they can depend irreducibly on group-correlated information of the source action. No route establishes it.

## Attempts

Replace source information by a relative cycle operator. Conditional
averaging preserves the surplus trace exactly, but the determinantal
law of that operator can lose connectivity even for a finite extension
with a connected source treeing. The relative-exchange artifact proves
this and gives a working finite-block replacement in the same known
family. Its generalization would need a bound on the actual repair
graphing, not just a dimension count.

Reveal the flags. The localization theorem produces an intermediate factor on which the defect is exactly zero, but it resolves the penalty by retaining information; the flags remain measurable in an extension of the base, and fixed price needs an argument that forgets them (reuse-compression artifact, Section 7).

Copy the source process outright. Reproducing the finite statistics of an arbitrary free action inside a Bernoulli action is impossible (`fpbs-source-statistics-not-reproducible-in-bernoulli`), so a transport theorem may preserve only the achievable cost. The reuse programme is the attempt to say which part of the process actually has to be preserved.

Simulate the flags by independent colouring. The finite conditional-noise simulation removes independent Bernoulli information for every finitely generated group, but it needs the added coordinates to be conditionally independent once the base point is fixed. The observations f(yg) inside the forgotten a-coordinate are generally not independent, and sampling group-coherent source states independently at different vertices need not define the original extension or preserve its routing certificates; averaging over a whole hidden action can destroy connectivity and the repeated-use discount (reuse-localization artifact, Sections 5 and 7; response 53).

Push the information limit for a fixed plan. Conditional Jensen gives only nonnegativity of the defect, and the L1 contraction gives monotonicity along an increasing information chain; neither supplies an upper bound tending to zero, and the optimisation is over plans that change as they approach optimal cost (reuse-compression artifact, Sections 2 and 3).

Make the signal negligible. Relative to a cost-one hyperfinite spine the flags can be supported on a set of arbitrarily small measure, but a rare connector may serve many requests: a hypothetical gap Delta with relative budget b forces traffic at least Delta/b, and no uniform traffic bound is available (reuse-localization artifact, Section 6).

Unite independent copies of a source graphing. This preserves generation but
can destroy optimality even when every input attains the action cost. The
September 10 calculation in the reuse-compression artifact, Section 8,
uses M Nielsen bases of F_2 over a finite trivial extension: each input
costs 2, whereas the union of k independent copies costs exactly
1+M(1-(1-1/M)^k), tending to M+1. The infinite union is base measurable,
but its excess cost is arbitrarily large. A successful version must also
remove edges with a proved cost and connectivity bound. The example does
not exclude such removal and is not a counterexample to this open claim.
