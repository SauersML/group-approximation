---
rg: 2
id: leavitt-module-dual-actions-are-self-squares-off-bernoulli
kind: claim
title: The Leavitt algebra's dual action over its unit group is a free ergodic self-square, and no Leavitt-module action is a Bernoulli factor
distinct_from:
  stable-finiteness-failure-is-algebraic-bernoulli-absorption: that is self-absorption of a Bernoulli shift, produced by a one-sided inverse in the group algebra and passing the stabilizer test; this is the exact doubling of an action produced by the Leavitt relation itself, which fails the test.
  leavitt-units-have-zero-rokhlin-entropy-supremum: that is the zero side of the Rokhlin entropy dichotomy for all free actions of the same group; this constructs one explicit free ergodic action isomorphic to its own square and computes nothing about entropy.
  bernoulli-factor-algebraic-actions-have-finite-stabilizers: that is the general stabilizer test for algebraic Bernoulli factors; this applies it to every module over the Leavitt algebra.
---

**ESTABLISHED** by [[leavitt-module-dual-actions-self-square-proof]].

Let `L = L_(F_2)(1,2)` with generators `s_0, s_1, t_0, t_1`, `t_i s_j = delta_ij` and
`s_0 t_0 + s_1 t_1 = 1`, and let `U = L^x`. For a countable left `L`-module `M`, let `U` act on
`X_M = Hom(M, F_2)`, with Haar measure, by `(u.x)(a) = x(u^-1 a)`.

1. **Self-square.** `X_L ≅ X_L × X_L` as compact `U`-groups, hence as p.m.p. actions. So
   `X_L ≅ X_L^k` for every `k >= 1`.
2. **Free and ergodic.** `U ↷ X_L` is essentially free and ergodic.
3. **Off the Bernoulli world.** For every nonzero `L`-module `M`, `U ↷ X_M` is not a factor of any
   Bernoulli shift over `U`. In particular `X_M × B` is never isomorphic to a Bernoulli shift `B'`,
   for any Bernoulli shift `B`.

**Reading for the negative direction.**
- The Leavitt relation creates information for free in the most literal sense: one explicit free
  ergodic action of a nonsofic group is two independent copies of itself. Under any additive
  entropy with finite values it would have entropy `0` or `∞`.
- Part 3 is a sharp obstruction. The doubling `L ≅ L ⊕ L` never produces a Bernoulli complement,
  because every nonzero `L`-module element `s_0 m` is fixed by the infinite corner group
  `iota_1(U) = { s_0 t_0 + s_1 b t_1 : b in U }`. So a Bernoulli shift with different base entropy
  cannot be split off along any Leavitt module.
- What survives inside the Bernoulli world are modules over `F_2[U]` that are not `L`-modules. The
  algebraic self-absorptions of Bernoulli shifts among them are exactly the stable finiteness
  failures (`stable-finiteness-failure-is-algebraic-bernoulli-absorption`). The defect
  `t_0 s_0 = 1 != s_0 t_0` lives in the quotient `L` of `F_2[U]` and is not known to lift
  (`direct-finiteness-not-inherited-by-quotients`, `leavitt-unit-group-algebra-not-directly-finite`).
