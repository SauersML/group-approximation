---
rg: 2
id: fpbs-correlated-reuse-flags-removable
kind: claim
title: Group-correlated reuse flags can be removed without increasing completed cost
artifacts:
  - research/artifacts/fpbs/docs/cost-rank-duality.md
  - research/artifacts/fpbs/docs/finite-fiber-cost-descent.md
  - research/artifacts/fpbs/docs/relative-cycle-exchange.md
  - research/artifacts/fpbs/docs/fixed-price-reuse-localization.md
  - research/artifacts/fpbs/docs/fixed-price-reuse-compression.md
  - research/artifacts/fpbs/responses/55_0909-215618.md
---

**OPEN.** For a factor map pi from a free action Y onto a free action X of a finitely generated group, and in particular for the projection a x b -> b onto a Bernoulli action, prove that there are finite routing plans on Y with budget tending to C(Y) whose conditional traffic defect for pi tends to zero. Equivalently, prove that every free extension generated over its base by the orbit name of one binary observable preserves cost; equivalently, that the pushforwards of the unused-edge measures and of the repeated-use measures can be made asymptotically singular while the near-optimal edge budget is preserved.

This is the isolated remaining step of the reuse programme. The savings to be preserved are those of a connection used many times and paid for once, and the question is whether they can depend irreducibly on group-correlated information of the source action. No route establishes it.

## Attempts

Dualize optimized subgraph cost as a matroid rank. The proved
`fpbs-cost-subgraph-rank-obstruction` rules out a monotone or
submodular rank that both attains cost and is consistent under
edge restriction. Two commuting extensions of the F_r treeing
give costs 1,1,r,1 for A,B,their intersection,their union.
Even zero relative completion cost leaves the retained treeing's
edge cost r. An ambient-dependent dual certificate remains possible,
but the graphing-matroid theorem for planar duals does not supply
one for an arbitrary Cayley graph. The precise literature scope
and the failed extra axiom are recorded in the cost-rank artifact.

Repair connections shared by whole components. The proved
`fpbs-infinite-contact-zero-relative-cost` constructs arbitrarily
cheap repairs on the original action when the graph of infinite
contacts between retained components is connected. This can replace
the traffic construction's direct demand repairs. The shared-repair
artifact also proves that determinantal cycle deletion leaves no
finite cut in its component quotient. A recursive parallel-path
counterexample rules out inferring sparse-sprinkling connectivity
from that weaker cut property alone. Suitable contacts at the
source budget, or a stronger repair mechanism exploiting the
actual determinantal law, remain to be constructed.

There is now a sharper limitation of this repair criterion in
Sections 6--7 of the same artifact. The uniform forest on F_2 x Z
has zero optimized relative repair cost in its free forest-times-
Bernoulli action, but sparse independent sprinkling fails by BLPS
Theorem 13.7. Rare whole columns and layers give an explicit
dependent repair on an enlarged space. Their law cannot be copied
into Bernoulli because of a nontrivial Z-invariant marking event.
Thus neither infinite contacts nor reproduction of that successful
helper law can be required as a universal route to cost preservation.

Start with finite fibers, then pass to a limit. The proved
`fpbs-finite-fiber-cost-bound` gives C(X)-1<=q(C(Y)-1) for a uniform
q-point factor. This excludes finite-to-infinite cost loss in that
setting and proves equality at cost one. Exact equality at arbitrary
cost is equivalent, over all groups, to finite-index multiplicativity
for specified free actions; the finite-fiber artifact proves both
directions without assuming either universal assertion. Complete-section
induction alone does not supply that equality. Section 10 of the
conditional-traffic artifact does prove C(Z_r) decreasing to C(Y)
when increasing factor sigma-algebras exhaust Y over a finite-cost
base. A tower of cost-preserving finite-fiber factors would therefore
suffice where it exists. Neither cost preservation at the finite stages
nor such a tower for arbitrary binary symbolic extensions is proved.

Choose an approximately equivariant label in each finite fiber.
Sections 5--6 of the finite-fiber artifact prove C(X)<=B+W, where
W counts routing traffic across label switches. But the explicit
two-point chi-extension of Bernoulli F_2 x C_2 satisfies
r+W>=2-sqrt(3) for every labeling and every finite plan for the
five symmetric generator demands, while both costs are 3/2.
Therefore requiring vanishing W together with vanishing uncovered
requests is too strong. W can overcount actual missing connections;
this rules out that criterion, not all selection-based repairs or
vanishing of the conditional defect J required by the open claim.

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
