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
* **Spherical transplant on tree products (swarm-0917-w14, group-rings;
  exact identity, no counterexample).**
  - On `X = T_{a_1} □ ... □ T_{a_r}`, `τ_p` is bi-radial. Kesten's corner
    together with a Schur test with weight `Φ = ⊗ φ_{a_i}` gives
    `||T_p||_{2->2} = Σ_t τ_p(t) |S_t| Φ(t)` exactly
    (`fpbs-tree-product-two-point-norm-is-spherical-sum`).
  - So `p_c < p_{2->2}` on `X` is one scalar series question, and
    `p_c < p_{2->2}` implies (IS) through [Q].
  - The test for a counterexample was whether the w12 pointwise failures
    `τ_pc(o,z_k) gr^{2k} >= R^k` on T3xT10 make the series diverge. They do
    not. The diagonal weight is `Θ(k^2 18^{k/2})`, so the per-step decay
    threshold is `18^{-1/2} ≈ 0.236`. The 2-path blocks give only
    `2p_c^2 - p_c^4 <= 0.0247`.
  - **Where it dies:** the lower side needs `τ_pc` at the tempered scale
    `Φ`, and no pointwise block estimate comes within `9.5^k` of it. The
    upper side, convergence at `p_c + ε`, needs a pointwise bound
    `τ_pc(t) <= Φ(t) · Π (a_i-1)^{-δ t_i}`. Sharpness gives only the
    infimum `κ_pc(n)`, and w12 shows `gr`-decay itself fails pointwise.
    This is the same missing critical-l2 input as the Russo-BK and l^q
    routes.
  - It does not bear on the goal for these graphs, where `p_c < p_u` is
    already known (Hutchcroft, nonunimodular).
* **Thermodynamic-formalism / shape transplant (swarm-0917-w15, symbolic-dynamics).**
  The idea is to treat `log lambda` like a pressure. A pressure is a pointwise
  limit of convex log-partition functions, so it is convex and hence
  continuous. The same property for `lambda` would give (IS) without any
  uniformity in `n`. On `T_d`, `log lambda` is indeed convex in `log p`.
  **Where it dies** (`fpbs-walk-rate-shape-classes-fail`, established):
  - Take any reparametrisation `phi` of `p` and any increasing transform `psi`
    of `lambda`.
  - **Concavity** fails on every nonamenable Cayley graph. The reason is the
    subcritical plateau `lambda = rho` on `(0,p_c]` together with
    `lambda >= p`.
  - **Convexity** fails whenever `p_u < 1`. The reason is the saturation
    plateau `lambda = 1` from the floor `theta^2`.
  - **Convexity also fails on `T_3 box K_2`, where `p_u = 1`** (exact rate
    formula): `log lambda` is concave on `(0.70, 0.995)`, because parallel
    rails give `1 - mu ~ (1-p)^2`.
  - **Restricting the shape** to `{lambda < 1}` or to `(0,p_u)` is vacuous in
    the collapse scenario.
  - **The invariant is these two forced plateaus.** Any closed shape class
    containing steep continuous ramps contains the collapse profile. So a
    closed route must carry a quantitative modulus at `p_c`.
* **Invariant-partition / co-spectral-radius transplant (swarm-0917-w16,
  transplanter, reframing; obstruction).** The idea is to read `lambda(p)` as
  the co-spectral radius of the invariant random cluster partition `Pi_p`,
  i.e. `a_n = P(X_n in K(o))`. This is the analogue of `P(X_n in H)` for an
  invariant random subgroup `H`. The hope was to import the
  Abért–Glasner–Virág Kesten theorem for IRS (arXiv:1201.3399, co-spectral
  radius `= rho` iff `H` is amenable a.s.): a structural property of `Pi_p`
  would pin `lambda` near `rho` just above `p_c`.
  - *Proved (standard, via Schramm's mass transport).* For any
    `Gamma`-invariant random partition with a.s. finite classes,
    `a_n = E[|K(o)|^(-1) <P^n 1_K, 1_K>] <= rho^n`. By monotone convergence
    in each `a_n` and Fekete (`lambda = sup_n a_n^(1/n)`, supermultiplicativity
    from Harris), the rate class `R_r = {a_n <= r^n for all n}` is closed under
    increasing unions of invariant partitions. So hyperfinite partitions have
    `lambda <= rho`. Since `Pi_p` is the increasing union of `Pi_q` for
    `q < p`, this gives only left-continuity of `lambda`.
  - *Right side.* `Pi_(p_c)` is the decreasing limit of `Pi_p` as `p`
    decreases to `p_c`. Pairwise this limit is exact:
    `0 <= tau_p(o,x) - tau_(p_c)(o,x) <= theta(p) -> theta(p_c) = 0`.
    So (IS) is exactly the statement that `R_r` survives this decreasing
    limit for every `r > rho`.
  - **Where it dies.** `R_r` is not closed under pairwise-convergent
    decreasing limits. The state-level collapse witness of
    `fpbs-two-point-state-axioms-admit-collapse` (every group, with (T7)
    pairwise right continuity) and the event-level spine families of
    `fpbs-soft-collapse-iff-invariant-sparse-spines` are such limits with
    `lambda = 1` above `p_c`. The structural substitute fails too, because
    the AGV dichotomy is false for partitions. On `T_d`, for
    `p in (1/(d-1), 1/sqrt(d-1)]`, `Pi_p` has infinite nonamenable,
    non-hyperfinite clusters, yet `lambda = rho`. The reason is that
    `P(|X_n| = k)` is at most `poly(n) rho^n (d-1)^(k/2)`, so
    `E p^|X_n| = O(poly(n) rho^n)`. AGV's proof uses closure `H H = H`, which
    clusters lack. So no amenability or hyperfiniteness property of `Pi_p`
    characterises `R_r`, and the transplant reaches the same missing
    quantitative input at `p_c + 0` as every route above. No new node was
    written: the kill is the one already recorded by those two collapse
    nodes, and this bullet only records that the IRS dictionary adds
    nothing.
