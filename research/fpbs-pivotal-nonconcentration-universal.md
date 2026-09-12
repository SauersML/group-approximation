---
rg: 2
id: fpbs-pivotal-nonconcentration-universal
kind: claim
title: Every nonamenable Cayley graph avoids full critical pivotal sensitivity concentration
distinct_from:
  fpbs-pivotal-budget-universal: that is the uniform near-critical linear budget; this only forbids the whole asymptotic normalized budget from concentrating in some neighbourhood above criticality, and is strictly weaker.
---

OPEN. With the exact limit order of Section 2, prove that some epsilon>0 has B(epsilon)<-log rho for every nonamenable locally finite Cayley graph. The stronger B(epsilon)->0 would suffice but is not proved.

## Attempts

* **Deduce it from the pointwise budget.** `fpbs-pivotal-budget-universal`
  implies `B(epsilon) <= C log(1+epsilon/c)`, hence the stronger
  `B(epsilon) -> 0`. **Where it dies:** with the pointwise budget, at
  `fpbs-hierarchical-pivotal-amplification`. The integrated form is
  deliberately weaker, since it tolerates narrow high peaks that the
  pointwise bound forbids, but nothing in the archive proves it without the
  pointwise bound.
* **Use continuity in the parameter.** Critical clusters on a nonamenable
  Cayley graph are finite almost surely, so in the uniform-label coupling the
  root cluster is unchanged on a random positive interval above `c`;
  dominated convergence gives `a_n(c+epsilon) -> a_n(c)` for each fixed `n`,
  hence `lim_(epsilon->0) lim_R M_(n,R)(c+epsilon) = 0`. **Where it dies:**
  Proposition 4 of `research/artifacts/fpbs/exploration.md`, recorded as
  `fpbs-critical-pivotal-concentration-under-collapse`, computes the other
  order of limits under collapse and gets exactly `-log rho` for *every*
  `epsilon`. The two limits do not commute and no uniformity is proved, so
  the fixed-`n` continuity is consistent with the collapse rather than an
  argument against it.
* **Bound the total budget.** `fpbs-integrated-pivotal-total-budget` gives
  `0 <= M_(n,R)(1) <= log(1/c)` and `M_(n,R_n)(1) -> -log rho`. **Dead as an
  approach:** an `O(n)` total pivotal budget over the whole interval is
  already available and adds nothing; the entire question is where inside
  `(c,1]` that fixed mass sits.
* **Follow the bridge tree.** Pivotal distance is distance in the bridge tree
  of the configuration, which suggests an annealed estimate on that tree for
  random-walk endpoint pairs. **Where it dies:** Section 5 of the same note.
  Counting original bridges is insufficient by
  `fpbs-bridgeless-collective-fragility`, and the evolution of the bridge tree
  as the parameter increases is part of the problem rather than a correction
  to it.
