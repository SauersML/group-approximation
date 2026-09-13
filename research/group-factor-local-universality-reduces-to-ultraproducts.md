---
rg: 2
id: group-factor-local-universality-reduces-to-ultraproducts
kind: claim
title: A locally universal group factor exists iff every separable tracial von Neumann algebra embeds in an ultraproduct of group factors
distinct_from:
  some-countable-group-factor-is-locally-universal: that is the open existence question for one group; this proves it is equivalent to a statement about the whole class of group von Neumann algebras.
---

**Statement.**  The following are equivalent.
1. Some countable group `U` has `L(U)` locally universal.
2. For every separable tracial von Neumann algebra `N` there are countable
   groups `Gamma_1, Gamma_2, ...` and an ultrafilter `V` such that `N` embeds
   unitally and trace-preservingly into `prod_V L(Gamma_n)`.

**Proof.**  Route `group-factor-local-universality-ultraproduct-proof`: (1) ⟹
(2) is the constant sequence; (2) ⟹ (1) takes the free product of countably
many witnessing groups, one for each rational moment table.
