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
* **Assume the critical l2 gap.** If `p_c<p_(2->2)`, then for some `p0>p_c`
  the conditional pivotal count is at most a constant `C_0` for all `p<=p0`,
  `n>=1` and `R>=n`. The integral in (IS) is then at most
  `C_0 log((p_c+epsilon)/p_c)`, so (IS) holds
  (`fpbs-l2-gap-cayley-graphs-satisfy-pivotal-kernels`); every such graph
  already has `p_c<p_u`. **Where it dies:** `C_0` comes from a full-space
  bubble that is infinite at every uniqueness parameter, so bounding it above
  `p_c` already proves nonuniqueness (Section 6 of
  `research/artifacts/fpbs/docs/pivotal-kernel-ordering-2026-09-12.md`).
* **Calibrate on a host with product structure but no transitivity (calibration,
  swarm-0917).** `fpbs-walk-rate-holes-fail-on-unimodular-random-graphs` works on
  the stretched Angel--Hutchcroft graph `H~(M)` (arXiv:1710.03003, Proposition
  4.2). It is a bounded-degree unimodular random graph with `p_c=p_u=q`.
  * *Proved there, accepted by referees (the node is still OPEN).*
    - A deterministic Cheeger bound `Phi >= 1/(DM(D+1))`, so `rho_bar<1`.
    - The annealed Schramm lemma by mass transport, `a_n(q) <= rho_bar^n`, without
      critical finiteness.
    - The uniqueness floor `a_n(p) >= (E_mu_hat theta_p)^2`, from positivity of
      the lazy environment operator.
    - Hence the annealed rate jumps: `lambda_hat(q) <= rho_bar < 1 = lambda_hat(p)`
      for every `p>q`.
  * *What fails on H~.* Annealed (IS), finiteness of green-visit, the root-uniform
    pivotal budget and cheap certificates all fail on `H~` in annealed,
    root-uniform form.
  * *Refuted overreach (2026-09-17).* The class-kill does not follow. It claimed
    that every argument using only product-measure, mass-transport and expansion
    inputs would prove (IS) on `H~` "run with root averages". No translation
    lemma was given, and root averaging does not commute with nonlinear steps
    such as supermultiplicativity. So "product structure and transitivity are
    jointly necessary" is unproven.
* **Group-ring / spectral-measure transplant (swarm-0917).** Write
  `a^L_n(p) = <pi_p(mu_L)^n xi_o, xi_o>` in the cluster Koopman representation
  on `L2` of (configuration, cluster) pairs. Here `xi_o = 1{o in K}`, and
  `tau_p` is the matrix coefficient of `xi_o`. Then `lambda_L(p)` is the top of
  the spectral measure `nu_p` of `xi_o`. The invariant vectors are
  `C 1_(Y_inf)` under uniqueness and `0` otherwise, by indistinguishability,
  and they carry the atom `theta^2` at `1`. So (IS) says: the top of
  `nu_p` restricted to `[0,1)` tends to `rho_L` as `p` decreases to `p_c`.
  **Where it dies:** in general nothing controls how `nu_p` moves in `p`.
  Weak continuity of `nu_p` (each moment is right-continuous at `p_c`) does
  not control the top of the support, the same order-of-limits failure as
  above. **What it gives instead:** where a spectral gap is uniform in `p`,
  the transplant is exact. On Kazhdan Cayley graphs
  `a^L_n(p) <= theta^2 1{U_p} + eta^n` with `eta = 1-kappa^2/(4|S|)` for all
  `p` (`fpbs-kazhdan-uniform-walk-decorrelation`). There NC and green-visit
  are equivalent to `p_c<p_u`, so (IS) is at least as strong as the
  separation itself on the whole (T) class, and it cannot be reached through a
  weaker intermediate kernel there.
* **Logic-computability transplant: certify (IS) from finite-ball data
  (swarm-0917-w6).** In the space of marked groups, `lambda(G,q)` is a
  supremum of ball-local continuous functions `a_(n,R)^(1/n)`. So
  `{lambda <= r}` is closed (Pi^0_1), and the hope is a Sigma^0_1 (open)
  certificate for `lambda(q) < 1` or for nonuniqueness. **Where it dies:** at the
  transfer to an amenable approximant
  (`fpbs-pu-open-certificates-pinned-at-pc`).
  - The derived-series quotients `S_k = F_2/F_2^(k)` converge to `F_2` with
    `p_u(S_k) = p_c(S_k) -> 1/3`, while `p_u(F_2) = 1`. For `q in (1/3,1)`,
    `lambda(S_k,q) = 1` for large `k` but `lambda(F_2,q) < 1`.
  - By relative Burton–Keane and Easo–Hutchcroft locality, every open certificate
    that is sound near `G` certifies only `p <= p_c(G)` whenever `G` is a limit of
    amenable groups. That includes `F_2`, surface groups and `G x Z^2` for every
    residually finite `G`.
  - So any proof of (IS), or of `lambda(q) < 1` at some `q > p_c`, on these
    graphs must consume a hypothesis that is not a marked-group neighbourhood,
    such as `rho <= r < 1` used quantitatively, or infinite-information operator
    data.
  - (IS) stays OPEN; this is a class kill for ball-local certificates, not a
    counterexample.
* **l^q two-point Hölder transplant (swarm-0917-w5).** Hölder against the heat
  kernel and interpolation between l^1 and l^2 give `a_n(p) <= rho^(2n/q)`
  with constant 1 whenever `tau_p(o,.)` is in l^q with `q >= 2`
  (`fpbs-lq-two-point-bounds-walk-rate`, established). In particular
  `lambda = rho` on `p <= p_2`, which extends Hutchcroft's `p <= p_{2->2}`.
  This reduces (IS) to the vector-level hole [Q]: `p_c < p_q` for every
  `q > 2` (`fpbs-two-point-lq-threshold-gap-universal`, route
  `fpbs-integrated-sensitivity-via-lq-two-point`). [Q] is implied by the
  operator gap `p_c < p_{2->2}`.
  **Where it dies:** openness of `{Z_q < infinity}` through `p_c`. The
  Russo-BK majorant is again a critical l^2-type quantity. No critical l^q
  input is importable, because arXiv:1605.05301 bounds only the infimum
  `kappa_{p_c}(n)`.
  **Calibration:** the kernel `1_H` (H infinite amenable) has rate `rho` but is
  in no l^q, so a failure of [Q] would not refute (IS). Artifact:
  `research/artifacts/fpbs/docs/lq-two-point-walk-rate-2026-09-17.md`.
