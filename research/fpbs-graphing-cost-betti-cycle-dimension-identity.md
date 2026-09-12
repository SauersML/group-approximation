---
rg: 2
id: fpbs-graphing-cost-betti-cycle-dimension-identity
kind: claim
title: Graphing cost splits exactly into one, the first L2 Betti number, and the finite-cycle dimension
distinct_from:
  fpbs-fusf-not-connected-on-some-cayley-graphs: that obstruction kills the attempt to realize cost as one plus the first L2 Betti number by deleting edges along an invariant random forest; this one is a dimension identity for a given graphing and asserts no such deletion scheme
  fpbs-amen2-betti-cost-input: that imports the one-sided Gaboriau inequality between the first L2 Betti number and cost minus one; this one is the exact decomposition of the cost of a given bounded-degree graphing, whose third term is the von Neumann dimension of its finite-cycle space
artifacts:
  - research/artifacts/fpbs/docs/cost-cycle-structure.md
  - research/artifacts/fpbs/responses/50_0909-211018.md
---

For a bounded-degree graphing Phi with infinite components generating R, c(Phi) = 1 + beta_1(R) + z(Phi), where z(Phi) is the von Neumann dimension of the closed span of finite simple-cycle chains and beta_1 is the first L2 Betti number of the relation, which for a free action equals that of the group. Writing g(R) = C(R) - 1 - beta_1 >= 0 for the excess over the homological lower bound, z(Phi) = g(R) + eps with eps = c(Phi) - C(R). All possible action dependence of cost lies in g.

The excess has an exact description as a failure to interchange limits. Let z_L be the dimension carried by cycles of length at most L and tau_L = z - z_L. Along any near-minimizing sequence of bounded-degree graphings, tau_L tends to g for each fixed L, while for each fixed graphing tau_L tends to zero as L grows. Hence C(R) = 1 + beta_1 as soon as one near-minimizing sequence satisfies lim over L of limsup over n of tau_L = 0, and conversely that condition follows from the equality. The gap is therefore not hidden in bounded-length cycle patterns of near-minimizers, which carry vanishing edge measure.

Status records a written deduction over imported L2 theory, not independent validation.
