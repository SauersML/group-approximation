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
