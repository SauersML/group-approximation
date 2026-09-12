---
rg: 2
id: fpbs-integrated-sensitivity-universal
kind: claim
title: Every nonamenable Cayley graph has vanishing integrated sensitivity at criticality
artifacts:
  - research/artifacts/fpbs/critical-cluster-stability.md
---

OPEN target IS from Section 6. The normalized, integrated pivotal sensitivity must tend to zero as the parameter interval shrinks. Equivalently lambda(p) tends down to rho as p decreases to pc. Neither universal proof nor counterexample is supplied. This is a stronger sufficient target than merely ruling out saturation at -log rho.

## Attempts

* **Couple the critical clusters and control the entire finite spectral
  measure (2026-09-09).** `fpbs-critical-cluster-stability-modulus` gives
  the exact probability that a critical cluster changes under sprinkling.
  `fpbs-finite-spectrum-total-variation-continuity` strengthens fixed-time
  continuity to total variation convergence and uniform rho-normalized
  continuity of finite-cluster moments. **Where it dies:**
  `fpbs-uniqueness-spectrum-critical-remainder` shows that even the full
  uniqueness-phase measure can converge in total variation while a
  vanishing atom at 1 changes its moment growth rate. Section 5 of the
  cited artifact supplies an exact two-atom control. Applying the finite
  moment estimate to full connectivity would omit the infinite-cluster
  term. The universal (IS) hypothesis remains OPEN.

* **Read it off the exact rate identity.** `fpbs-integrated-pivotal-rate-identity`
  proves that the iterated limit of the normalized integrated sensitivity
  equals `log(lambda(p)/rho)`, where `lambda(p)=lim_n a_n(p)^(1/n)` exists by
  FKG supermultiplicativity and `lambda(p_c)=rho` by Schramm's lemma. So (IS)
  is exactly right-continuity of `lambda` at `p_c`. **Where it dies:** the
  identity is an equality, so it is equally consistent with the collapse
  scenario, in which `lambda(p_c)=rho<1` and `lambda(p)=1` for every `p>p_c`
  by the FKG lower bound `theta(p)^2`. Section 6.3 of
  `research/artifacts/fpbs/exploration-pivotal-projections.md` states that
  continuity of each fixed-`n` connection probability does not imply
  continuity of the exponential rate; the limit `n -> infinity` is
  load-bearing.
* **Inherit it from the pointwise budget.** `fpbs-pivotal-budget-universal`
  implies (IS), since the integral is at most `C log((p_c+epsilon)/p_c)`.
  **Where it dies:** with the pointwise budget, at
  `fpbs-hierarchical-pivotal-amplification`. (IS) is the weaker target
  precisely because it permits narrow spikes, and no proof of it avoids the
  pointwise route.
* **Extend the successful geometries.** The cactus theorem
  (`fpbs-cactus-pivotal-bound`) and the block-graph bound give (IS) wherever
  they apply, and the regular-tree operator calculation
  (`fpbs-regular-tree-dyadic-three-halves`) settles the parallel projection
  target on trees. **Where it dies:** both use the absence of multiscale cycle
  overlap or a branching cluster-size law. Neither survives on a general
  nonamenable Cayley graph, and the hierarchical control shows the first
  cannot be repaired by degree or adjacency hypotheses.
* **Settle for strict inequality.** It suffices to place the limit strictly
  below `-log rho` rather than at zero; this is
  `fpbs-pivotal-nonconcentration-universal`. Neither version is proved, and
  the collapse forces exactly the boundary value `-log rho`, so no slack is
  visible from this side.
