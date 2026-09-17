---
rg: 2
id: fpbs-bernoulli-morse-collapse-criterion-proof
kind: route
title: König's lemma turns well-founded cell matchings into generating subgraphings, and shortest recovery words give depth-one matchings over long relators
target: fpbs-bernoulli-morse-collapse-criterion
requires:
  - fpbs-graphing-cost-betti-cycle-dimension-identity
  - fpbs-bernoulli-maximal-cost
  - one-relator-group-cost-equals-first-l2-betti-plus-one
artifacts:
  - research/artifacts/fpbs/docs/bernoulli-morse-collapse-criterion.md
---

Written derivation. The details are in Sections 2–4 of the artifact.

1. **Cost of the subgraphing.** On each piece of cells of a fixed type matched to a fixed letter, the matching is a
   fixed group translate. So it preserves measure, and since it is injective, the removed edges have measure
   `mu(M)`.
2. **Generation.** A recovery tree has branching at most `k_max - 1` and no infinite branch, so König's lemma makes it
   finite. Induction on height shows that every removed edge joins points equivalent under the remaining graphing.
3. **The upper bound on mass.** Apply the identity to the remaining graphing and to `Phi_S`. This gives
   `|S| - mu(M) >= 1 + beta_1` and `z(Phi_S) = |S| - 1 - beta_1`. At deficit zero, add Abért–Weiss maximality
   (`fpbs-bernoulli-maximal-cost`) to get fixed price.
4. **Monotonicity.** Matchings for a smaller list are matchings for a larger one.
5. **The limit.** For a generating subgraphing, match each removed edge whose shortest recovery word is shortlex-least
   of length below `L` to the cell reading that edge followed by the word. This matching is injective, its children
   are empty, and its mass increases to the removed measure.
6. **The proper-power ceiling.** Two matched cells on one boundary cycle make each matched edge a child of the other,
   so there is an infinite chain. Mass transport along `x -> w^{-1}.x` then bounds the mass by `1/m`. The one-relator
   value `beta_1 = |S| - 1 - 1/m` is imported from `one-relator-group-cost-equals-first-l2-betti-plus-one`.

This is dependency bookkeeping over a written proof, not a formal verification.
