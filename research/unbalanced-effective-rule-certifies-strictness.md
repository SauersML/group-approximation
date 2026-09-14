---
rg: 2
id: unbalanced-effective-rule-certifies-strictness
kind: claim
title: A left-invertible realization whose effective encoder rule is unbalanced is strict, so unbalanced designs need only their memory letters to survive
distinct_from:
  strict-automata-live-on-canonical-table-groups: that decides strictness through surviving reverse hinge words for every minimal reverse partition; this certifies strictness of an unbalanced rule from the forward table and the memory letters alone, examining no reverse product.
  every-injective-ca-has-uniform-single-site-output-law: that is the open goal-equivalent statement that injective automata have uniform site laws; this is the elementary direction applied to designs, turning a biased rule plus a forward-sufficient table into a strictness certificate.
artifacts:
  - research/artifacts/unbalanced-design-memory-collisions-2026-09-12.md
---

**ESTABLISHED 2026-09-12** by `unbalanced-effective-rule-certifies-strictness-proof`.

Let `D = (A, S, M, nu, mu)` be a design and `E` a forward-sufficient partition. Let `rho` be a
realization with forward table `>= E`. Collapse `M` along the collisions of `rho(M)` to get the
effective rule `mu_rho`.

**Proposition.** If `mu_rho` is not balanced (some symbol does not have exactly
`|A|^(#classes - 1)` preimages), then `tau_rho` is injective and not surjective.

*Why.* `sigma_rho tau_rho = id` gives injectivity. A bijective automaton preserves the uniform product
measure (`bijective-ca-preserve-uniform-bernoulli-measure`), and its one-site law is `mu_rho` applied
to independent uniform symbols.

**Over the table group.** If `mu` is unbalanced and the elements `1`, `x_m` (`m != 1_M`) are pairwise
distinct in `U_E`, then `U_E` is not surjunctive. No reverse partition needs to be examined.

**Sofic quotients.** Every sofic quotient of `U_E` identifies memory letters in a pattern that
balances `mu`. The abelianization is one such quotient, computable from `E`.
- **Robustly unbalanced rules.** Suppose `mu` is unbalanced under every collapse with at least two
  classes. Over `F_2` this holds when the algebraic normal form is an affine part plus the top
  monomial. Then every sofic quotient kills every memory letter. For connected designs this leaves
  only table groups with no nontrivial sofic quotient, which is the situation of `R^x`
  (`leavitt-unit-group-has-only-trivial-sofic-morphisms`).

Artifact, Section 1.
