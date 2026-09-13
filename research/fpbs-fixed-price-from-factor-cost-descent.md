---
rg: 2
id: fpbs-fixed-price-from-factor-cost-descent
kind: route
title: Use factor cost descent and the product-action equivalence, then the countable passage
target: fpbs-fixed-price-universal
requires:
  - fpbs-correlated-reuse-flags-removable
  - fpbs-traffic-variational-cost-identities
  - fpbs-factor-invariance-equals-fixed-price
  - fpbs-fixed-price-countable-from-finitely-generated
artifacts:
  - research/artifacts/fpbs/docs/fixed-price-conditional-traffic.md
---

For each infinite finitely generated group, removability supplies plans
with B tending to source cost and J tending to zero for every free factor.
The exact traffic identities then give factor-cost preservation. The
product-action equivalence proves fixed price for that group. Apply the
separately OPEN countable passage for the universal target. This route
uses no reverse weak-containment assertion. Both unresolved premises
remain required; the route is not a proof of the universal conclusion.

**Restatement, not reduction (audit of September 12, 2026).** Over all free
factor maps of one finitely generated group, the first premise is
equivalent to fixed price for that group: the identities also give the
converse, through lifted base plans. So this route has the same logical
content as `fpbs-fixed-price-from-bernoulli-cost-equality`, namely
finitely generated fixed price plus the countable passage. It is a valid
deduction, not a reduction to a weaker premise. See the scope audit in
`fpbs-correlated-reuse-flags-removable`.
