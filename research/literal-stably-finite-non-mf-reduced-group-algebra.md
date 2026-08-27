---
rg: 2
id: literal-stably-finite-non-mf-reduced-group-algebra
kind: claim
title: Literal reduced group algebra is stably finite but not MF
distinct_from:
  exact-stably-finite-non-mf-reduced-group-algebra: This claim concerns the finitely presented group E and does not assert exactness; the other concerns the sofic witness W and adds exactness.
  literal-mf-radical-exact: This is a proved reduced-C-star consequence for E; the other is the open exact computation of E's group-theoretic MF radical.
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Sofic/LiteralNonMFEndpoint.lean
---

The concrete reduced group C-star algebra of the literal finitely presented
group `E` is separable, carries its canonical faithful tracial state, is
stably finite in every nonempty finite matrix amplification, and is not MF.
