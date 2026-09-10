---
rg: 2
id: fpbs-free-action-cost-at-least-bernoulli-cost
kind: claim
title: Every free action of a finitely generated group has cost at least its Bernoulli cost
artifacts:
  - research/artifacts/fpbs/docs/relative-cycle-exchange.md
  - research/artifacts/fpbs/docs/fixed-price-conditional-traffic.md
  - research/artifacts/fpbs/docs/fixed-price-reuse-localization.md
  - research/artifacts/fpbs/responses/55_0909-215618.md
---

**OPEN.** For every infinite finitely generated group, every free p.m.p. action a and a nontrivial Bernoulli shift b, prove C(a) >= C(b). With Abert-Weiss maximality, which supplies C(a) <= C(b), this is the missing half of fixed price in the finitely generated case. The comparison has already been sharpened to C(a x b) = C(a) <= C(b), so the whole question is the projection a x b -> b, which forgets the entire a-process.

## Attempts

Descend only the relative cycle surplus. The established
`fpbs-relative-cycle-operator-descent` gives a base positive contraction
K of exact trace c(H)-c(Phi) for a source generating graphing Phi inside
the lifted base graphing H. But
`fpbs-relative-cycle-dpp-disconnects` proves that determinantal deletion
using K can disconnect even for a Bernoulli base and a finite extension
with a source treeing. The relative-exchange artifact, Sections 2--3,
constructs this example and a successful alternative using connected
finite cyclic blocks with a tree quotient. Section 4 states the actual
deletion-minus-repair bill still needed in general. That bill is not
proved by its operator trace; no new premise is introduced just to
rename this comparison.

Impose common finite blocks before exchanging edges. The established
`fpbs-finite-block-forest-cost-normal-form` permits any prescribed
finite-block forest on the base and its lift on the source to be
included at arbitrarily small cost excess. This removes a special
finite-group hypothesis from the preparation step. It does not solve
the connector comparison: Section 5 of the relative-exchange artifact
proves D=q D_A for the original and normalized restricted cost gaps.
Making the block transversal small without a new estimate on D_A
therefore retains the entire possible gap.

Control cycle dimension in Bernoulli cost minimizers. The conditional route
`fpbs-bernoulli-lower-bound-from-cycle-tails` proves the comparison from the
open `fpbs-bernoulli-cycle-tail-compactness` and the established cost--Betti
lower bound. It would show C(b)=1+beta_1, a stronger assertion than Fixed
Price alone. The explicit F_r x Z reduced-circulation calculation in
`research/artifacts/fpbs/docs/cost-cycle-structure.md`, Section 8, verifies
a sufficient tail bound in that family, not for arbitrary Gamma.

Descend through the product. By the variational identities, C(b) = C(a x b) would follow from finite routing plans on a x b whose budgets approach C(a x b) and whose conditional traffic defect for the projection onto b tends to zero. The two probability-space coordinates are independent, but the orbit observations inside the a-coordinate are not, so the finite conditional-noise simulation that settles the other projection does not apply in reverse. The localization theorem reduces what must be transported to finitely many binary reuse flags, and the argument then stops at exactly that point (reuse-localization artifact, Sections 4 and 7; response 55, Sections 4 and 6).

Optimise a canonical graphing instead. Replacing the comparison by an action-independent cycle optimiser fails: the universal priority-deletion scheme converges to the free minimal spanning forest, whose density stays above the cost of a fixed-price-one group (response 47, Section 3, recorded in `fpbs-priority-deletion-density-above-action-cost`).
