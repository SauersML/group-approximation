---
rg: 2
id: fpbs-pivotal-budget-universal
kind: claim
title: Every nonamenable Cayley graph has a uniform near-critical linear pivotal budget
---

OPEN research hypothesis P2. There exist graph-dependent C>0 and p0 in (pc,1) such that for all n>=1, all R>=n and all p in [pc,p0], E[N_piv | o connects to X_n inside B_R]<=Cn. No universal proof is supplied.

## Attempts

* **Charge the pivotal count to graph distance.** The hope is that `D_p(x,y)`,
  the conditional expected pivotal count, behaves like a metric so that a
  bound along a geodesic accumulates. **Dead:** `fpbs-pivotal-triangle-fails`.
  On the nonamenable Cayley graph of `C_6 * C_2` with `S={a,a^(-1),b}` the
  hexagon reliabilities give `D_2 - 2 D_1 = 6/209 > 0` at `p=1/2`, and an
  exact rational bound shows the defect stays positive at the critical
  parameter, which the branching calculation locates in `(0.513,0.514)`. The
  route `fpbs-dead-local-pivotal-charging` is killed by this.
* **Count bridges at criticality.** **Dead:**
  `fpbs-dead-bridge-count-at-criticality`. `fpbs-long-detours-with-no-bridges`
  gives a connected bridgeless model on `T_(2r) x Z` with divergent mean
  replacement-route length, and `fpbs-bridgeless-collective-fragility` shows
  its thinning threshold tends to one. A critical bridge count therefore
  controls neither the near-critical count nor resilience.
* **Prove it structurally and extend.** It holds with the optimal constant
  `1+exp(-2)` on every locally finite cactus, including in induced finite
  balls (`fpbs-cactus-pivotal-bound`,
  `fpbs-cactus-finite-ball-pivotal-budget`), and with constant `b` on graphs
  assembled from blocks of at most `b` edges. **Where it dies:**
  `fpbs-hierarchical-pivotal-amplification`. The recursive degree-three
  networks `J_k` have *adjacent* terminals, connection probability tending to
  about `0.992`, and conditional pivotal count growing like `0.0228 k` at the
  fixed parameter `p*=0.95841...`. Neither adjacency, bounded degree, nor rare
  conditioning bounds the count; the successful classes are exactly those with
  no multiscale cycle overlap, and a nonamenable nontransitive augmentation
  preserves the obstruction.
* **Ask for less.** Response 8 shows this pointwise hypothesis is stronger
  than the goal needs: `fpbs-integrated-pivotal-total-budget` already gives
  `M_(n,R)(1) -> -log rho` over the whole parameter interval, so only the
  *location* of the sensitivity is at issue. The work moved to
  `fpbs-pivotal-nonconcentration-universal` and
  `fpbs-integrated-sensitivity-universal`, which this claim implies and which
  are not known to be strictly weaker in any useful sense.
* **Assume the critical l2 gap.** On every Cayley graph a BK bubble, split at
  the connectivity operator by Cauchy–Schwarz, gives
  `E_p[N_(n,R)|E_(n,R)] <= 2 d ||T_p||_(2->2)^2` for all `n>=1` and `R>=n`
  (`fpbs-l2-gap-gives-bounded-pivotal-counts`). So the budget holds, with a
  count bounded independently of `n`, on every Cayley graph with
  `p_c<p_(2->2)` (`fpbs-l2-gap-cayley-graphs-satisfy-pivotal-kernels`). That
  class includes hyperbolic groups and the non-cactus products `T_k x Z^m`
  (`fpbs-pivotal-kernels-hold-on-known-gap-test-graphs`), but all of them
  already have `p_c<p_u`. **Where it dies:** the bound passes through a
  full-space bubble `W_n(p)` that is infinite at every uniqueness parameter,
  so a bound on it above `p_c` already certifies nonuniqueness. The
  finite-radius bubbles are finite but increase to `W_n`, so a universal proof
  must control the pivotal event uniformly over `R>=n` (Section 6 of
  `research/artifacts/fpbs/docs/pivotal-kernel-ordering-2026-09-12.md`).
* **Transplant the budget from approximating groups (finite-models).**
  * *The route.* The operator form of the budget transplants along local or
    marked limits exactly when the connectivity norms admit one common bound
    `M` at one common margin `delta` above `p_c`.
    - `||T_p||` is lower semicontinuous under local convergence.
    - The uniform gap class `U_(M,delta)` is closed.
    - Limits of `U_(M,delta)` satisfy `p_c<p_u` and the budget with count
      `2dM^2` (`fpbs-l2-gap-class-closed-under-local-limits`).
  * *Where it dies.* Proposition 4.1 of
    `research/artifacts/fpbs-l2-gap-local-limits-2026-09-17.md`: for finite or
    amenable approximants, `limsup Gamma_M(G_k) <= p_c(G)` for every `M`.
    - On such graphs `||T_p|| >= chi_r(p)`.
    - `chi_r` is ball-local.
    - `chi_r(p) -> infinity` for every `p>p_c(G)`.
  * *What remains.* Surviving approximants must be quantitatively gapped.
    - Qualitative theorems such as Choi–Seo with Hutchcroft's criterion stop at
      the common-margin step.
    - Closed certificate classes, such as free products on union generating
      sets, reach only themselves.
  * *The direct budget transplant.* `E_p[N|E]` is ball-local, but PB begins
    at `p_c(G) <= liminf p_c(G_k)`. The approximants would need the budget
    below their own critical points.
* **Transplant stability data of the Bernoulli action (stability-approximation,
  swarm-0917).**
  * *The dictionary.* The budget is a derivative in `p`. For an increasing
    event `E`, Russo's formula gives
    `E_p[N_piv 1_E] = sum_e P_p(e open, e pivotal) = p · d/dp P_p(E)`, so
    `E_p[N_piv | E] = p · d/dp log P_p(E)`. The hope was to bound this through
    stability data of the Bernoulli action: its Koopman representation, the
    spectral radius `rho`, Kazhdan constants, strong ergodicity, and membership
    in the class weakly contained in Bernoulli.
  * *Where it dies (invariant: the Koopman representation; step: the passage
    from `p_c` to `p_c+eps`).*
    - For every `p in (0,1)`, `L^2_0` of the edge shift decomposes into
      quasi-regular representations over finite edge sets. These have finite
      stabilizers, so the representation is contained in `infinity · lambda`
      independently of `p`.
    - Every datum above is therefore the same at `p_c`, at `p_u` and at `1/2`.
      The only `p`-dependence left is in observables such as `log P_p(E)`,
      whose `p`-derivative is the pivotal count itself, which is circular.
  * *What such data can reach.*
    `fpbs-fiid-soft-collapse-iff-fiid-sparse-spines` (Corollary E) shows that
    arguments using Bernoulli facts at `p <= p_c`, the soft axioms (S1)--(S4)
    and properties shared by factors of Bernoulli shifts fail on every group
    with factor-of-iid sparse spines. There they cannot give `p_c < p_u`, let
    alone the budget. On a class of groups they must prove
    `fpbs-no-fiid-sparse-spines-on-nonamenable-groups`, which by Corollary D
    already implies `p_c < p_u` there
    (`fpbs-benjamini-schramm-via-no-fiid-sparse-spines`).
  * *Why the known soft obstruction does not cover this.* The sheet spines of
    `fpbs-soft-collapse-iff-invariant-sparse-spines` are not weakly contained
    in Bernoulli (Proposition F of the new node). So this transplant was not
    already killed. What remains of it is exactly the no-FIID-spines hole,
    which contradicts the open claim `fpbs-kazhdan-sparse-spines`.
  * *Referee audit (2026-09-17).* Three lenses reviewed the supporting node
    `fpbs-fiid-soft-collapse-iff-fiid-sparse-spines`; lenses 1 and 3 refuted
    parts of it, so it is set back to OPEN. Lens 1: the "not strongly ergodic"
    half of Proposition F, bullet 2, fails for atomic height laws (sheets over
    `rZ + j` with iid connectors are strongly ergodic). Non-weak-containment
    survives, and the Theorem B height sets are atomless, so the bullet above
    is unaffected. Lens 3: the hole
    `fpbs-no-fiid-sparse-spines-on-nonamenable-groups` is false on `F_2 x Z^2`
    (fibrewise supercritical `Z^2` giants joined by iid `F_2`-edges give FIID
    sparse spines). So on groups with a normal `Z^2` factor, Corollary E rules
    out Bernoulli-weakly-contained soft arguments outright, and "what remains
    is the no-FIID-spines hole" holds only where that hole is not already
    false. All lenses found the Russo identity and the `p`-independence of the
    Koopman representation sound, so the dead-end verdict on this transplant
    stands and the target stays OPEN.
* **Symbolic-dynamics / pressure transplant: chemically truncated rates
  (b-p-bs1, 2026-09-17).**
  * *Idea.* Treat `lambda(p)` as a pressure and approximate the non-local
    potential `1_{e<->X_n}` by finite-range potentials. Pressures of
    finite-range potentials vary continuously.
  * *Where the pressure form dies.* Finite-range approximants of the
    connection event increase to it from below. Fekete gives only
    `lambda = sup`, so the approximation yields lower semicontinuity of
    `lambda`, not the right-continuity at `p_c` that (IS) needs.
  * *What survives (ESTABLISHED).* The natural finite-range approximants
    are the chemically truncated events `{d_omega(e,X_n) <= Ln}`.
    - Every open pivotal edge lies on one fixed certificate path, so PB holds
      on these events with `C=L` for free.
    - Their rates `lambda_L` are log-Lipschitz, with
      `lambda_L(p) <= rho (p/p_c)^L`, and `sup_L lambda_L = lambda`
      (`fpbs-truncated-walk-rate-log-lipschitz`).
    - (IS) is *equivalent* to rate saturation by slopes `L(epsilon)=o(1/epsilon)`
      (`fpbs-integrated-sensitivity-iff-subscale-chemical-saturation`).
    - Under collapse, walk connections at `p_c+epsilon` have chemical slope
      at least `p_c log(1/rho)/epsilon` (Corollary 3 of
      `research/artifacts/fpbs/docs/truncated-russo-lipschitz-2026-09-17.md`).
  * *Consequence for PB.* Any PB argument that bounds pivotal counts by
    certificate length proves a statement that is true on a collapse graph.
    PB is load-bearing only through the comparison of truncated and
    untruncated rates at sub-mean-field slope. PB itself stays OPEN.
* **Sum over walk lengths first (reframing, swarm-0917).**
  * *The kernel.* Summing (1.1) over `n<=R` gives
    `d/dp log A_R = E^tilt[N]/p`, where `A_R = sum_(n<=R) a_(n,R)` increases
    to `A(p) = sum_x g(x) tau_p(x)`. This is the expected number of visits of
    the walk to `C(e)`.
    - **GB** is a *bounded* Green-tilted pivotal count on `[p_c,p0]`.
    - **VIS** says `A(p)<infinity` for some `p>p_c`.
  * *Established* (`fpbs-green-visit-kernel-ordering`,
    `fpbs-green-visit-criterion-implies-nonuniqueness`, Section 3 of
    `research/artifacts/fpbs/docs/green-visit-kernel-2026-09-17.md`):
    - PB ⇒ GB ⇒ VIS ⇒ BS.
    - `p_c<p_(2->2)` ⇒ GB.
    - NC ⇒ VIS.
    - `tau_p in l2` ⇒ VIS.
    - `A(p_c) <= 1/(1-rho)`, and `A=infinity` at uniqueness.
  * *Consequence.* `fpbs-green-visit-criterion-universal` is the weakest
    kernel on the tip. A graph where VIS fails would refute this claim, IS,
    NC and the l2 gap there at once.
  * *Where it stops.* The pivotal content disappears.
    - GB and VIS have no pointwise-in-`n` control, so neither implies PB.
    - Like the bubble of Section 6, `A` is infinite at uniqueness, so VIS
      certifies nonuniqueness rather than deriving it.
    - RATE ⇒ VIS is not proved, and no converse is known.
* **Calibrate the bounded-count route on the tree (entropy-measure, swarm-0917 wave 5).**
  * *First idea, dropped.* Suppose a certificate sees the connection event only
    through three facts: it is increasing, it is supported on `E(B_R)`, and its
    probability is `P(E)`. Such a certificate cannot be uniform in `R`. Tribes
    events, the connection events of theta graphs, have probability at least
    `1-1/e` and conditional open-pivotal count at least
    `e^(-2) floor(log_(1/p)|E(B_R)|/2)`. This adds nothing new:
    `fpbs-hierarchical-pivotal-amplification` already defeats that class at
    bounded degree.
  * *Established* (`fpbs-tree-walk-pivotal-count-bounded-below-l2-threshold`).
    On `T_d` the random-walk count is the mean of `|X_n|` tilted by `p^k`. An
    `h`-transform of the radial chain by `(d-1)^(-k/2)` turns it into
    `sum k x^k sigma_k / sum x^k sigma_k`, where `x = p sqrt(d-1)` and
    `sigma_k <= d/(d-1)`. Ballot counts then show two regimes:
    - for `p<p_(2->2)=1/sqrt(d-1)` the count is bounded in `n`;
    - for `p_(2->2)<p<1` the count is at least `eps(p) n`, while
      `p_u=1`. The case `p=p_(2->2)` is not proved; numerically the count grows
      like `sqrt(n)`.
  * *Where it stops.* The n-free conclusion of
    `fpbs-l2-gap-gives-bounded-pivotal-counts` is sharp on `T_d`: it fails at
    every `p>p_(2->2)`, even though nothing happens to uniqueness there.
    - The budget is open only on graphs with `p_c=p_(2->2)`.
    - On such a graph, no method that proves n-free counts on `(p_c,p0]` can
      work unless that graph behaves unlike the tree. A proof must produce
      genuinely linear counts.
    - The tree does not refute PB, which holds on `T_d` with `C=1`. It gives
      no transitive example where counts beat `n`.
* **Transplant group-ring states and positive-definite functions (group-rings, swarm-0917 wave 5).**
  * *The route.* Read `tau_p` as a normalised positive-definite function on
    `Gamma`, a state on the group ring. Try to push the operator facts from
    `p_c` to `p_c + eps`:
    - GNS and Fell absorption put the critical state inside `lambda ⊗ 1`;
    - Harris gives supermultiplicativity;
    - the atom decomposition and the Kazhdan projection give walk bounds;
    - weak* continuity links the parameters.
    The goal was NC or VIS, which PB implies.
  * *Established* (`fpbs-two-point-state-axioms-admit-collapse`). On every
    nonamenable Cayley graph the family
    `f_p = theta(p)^2 + (1-theta(p)^2) tau_(p_c)` (for `p > p_c`) equals
    Bernoulli on `[0,p_c]` and satisfies eight state axioms (T1)–(T8):
    - positive definiteness;
    - mixed Harris supermultiplicativity, via a convexity identity with defect
      `a(1-a)(1-t(x))(1-t(y))`;
    - monotonicity;
    - the atom-plus-remainder walk decomposition;
    - Kazhdan decorrelation;
    - right weak* continuity at `p_c`;
    - the integrated infinite-volume Russo–BK inequality.

    Yet `lambda(f_p) = 1`, `A(f_p) = infinity` and `||F_p|| = infinity` for
    every `p > p_c`. This holds on `F_2` and on Kazhdan groups too.
  * *Where it dies.* At the continuation `p_c -> p_c + eps`.
    - The atom is upper semicontinuous under weak* limits, so it forces only
      `theta(p_c+) = 0`.
    - The rate, `A` and the operator norm are only lower semicontinuous and
      may jump.
    - The infinite-volume Russo–BK integrand is `+infinity` once
      `theta > 0`.
  * *What survives.* The non-state input that separates `f` from Bernoulli is
    the finite-ball polynomial truncation (4b)–(4e) of
    `fpbs-bk-majorant-integrated-sensitivity-is-critical-l2-proof`. On graphs
    with `||T_(p_c)|| < infinity`, `f` admits no truncation system. A proof
    of PB must use finite-radius events uniformly in `R`, as Section 6 of
    the pivotal-kernel ordering already required. The group-ring dictionary
    itself cannot supply that.
* **Transplant the operator-algebra dictionary (transplanter, swarm-0917 wave 5).**
  * *Dictionary.* `tau_p(x,y)=P_p(x<->y)` is a positive definite kernel, since
    `sum c_x conj(c_y) tau_p(x,y) = E sum_clusters |sum_{x in K} c_x|^2`. So
    `T_p` is a positive element affiliated with the group von Neumann
    algebra, and `a_n(p)=phi_p(P^n)` for the positive functional
    `phi_p = tau(T_p . )`. Let `nu_p` be the spectral measure of `P` under
    `phi_p`. Then `lambda(p)` is the top of `|supp nu_p|`. Russo–BK gives
    `d tau_p/dp <= d (tau_p * mu_S * tau_p)` entrywise.
  * *Easiest case (proved, not new).* If `||T_p||_(2->2)<infinity`, then
    `a_2n = tau(T^(1/2) P^2n T^(1/2)) <= ||T_p|| p_2n(o,o) <= ||T_p|| rho^2n`,
    so `lambda(p)=rho`. This is the proposition already recorded at
    `research/artifacts/fpbs/docs/pivotal-exploration.md` line 399.
  * *Break 1: the dictionary is not closed under the Russo–BK step.*
    - `nu_p` sees only `phi_p` restricted to `W*(P)`, through the conditional
      expectation `E(T_p)=f_p` on `L^infty(Kesten)`.
    - The majorant term `tau(P^n T P T)` equals `int x^(n+1) f_p^2 dk` only
      when `E` is multiplicative on `T_p`, that is when `tau_p` is a
      function of the walk. This holds for radial functions on a Gelfand
      pair, such as `T_d` with free generators.
    - In that case the closure gives
      `E[N|E] <= int x^(n+1) f^2 dk / int x^n f dk <= ||f||_infty <= ||T_p||`,
      which is again `fpbs-l2-gap-gives-bounded-pivotal-counts`.
    - For non-radial `tau_p`, the defect `tau(P^n T P T) - int x^(n+1) f^2 dk`
      has no sign, and no inequality inside `W*(P)` survives.
  * *Break 2: spectral sampling data cannot see the obstruction.*
    - Take `phi=1_H` with `H=<a>` in `F_2`. It is positive definite, and
      `p_2n(o,o) <= P(X_2n in H) <= (4n+1) rho^2n`, so it has sampling rate
      `rho`. Its convolution operator is nevertheless unbounded.
      Plateau data (`lambda=rho`) therefore never upgrades to critical L2.
    - Moments converge (`a_n(q)->a_n(p_c)` by dominated convergence), so
      `nu_q -> nu_(p_c)` weakly. That yields only *lower* semicontinuity of
      the top of the support, which is the wrong direction for VIS.
    - The jump is realised by `fpbs-soft-collapse-iff-invariant-sparse-spines`.
  * *Verdict.* On the positive side the operator-algebra transplant reduces to
    critical L2. On the negative side it is subsumed by the soft-collapse
    family and by the state-class obstruction of the group-rings lease. No new
    node was filed. Where it dies: the Russo–BK majorant is entrywise, not an
    operator inequality in `W*(P)`.
* **Wire the boundary (reframing via minimax labels, swarm-0917).**
  * *Idea.* Read (P1) as a reverse-hazard identity: `a_(n,R)` is the
    distribution function of the maximum label on the `MST(B_R)` path from
    `o` to `X_n`, so (P2) says `f/F <= Cn/q`. Ask whether the budget depends
    on the boundary condition by replacing `B_R` with the wired ball
    `B_R/S_R`, or more generally with `E_(n,R)` united with
    `{xi=1, o <-> S_R, X_n <-> S_R inside B_R}`, where `xi` is a
    Bernoulli(`eps`) coin.
  * *Result: established obstruction.* See
    `fpbs-wired-pivotal-budget-fails-universally`, with its complete route
    from (S) and `theta(p_c)=0`. On every nonamenable Cayley graph the wired
    budget fails, and it still fails at weight `eps_n >= e^(-delta n)` for any
    `delta < log(1/rho)`: `(1/n) sup_R sup_(q in [p_c,p0])` of the count tends
    to `+infinity`. The quantitative bound is
    `sup >= (n log(1/rho) + log eps + 2 log theta(p))/log(p/p_c)`.
    * *Class killed.* This kills every *boundary-blind* argument, meaning any
      argument whose steps (Russo, FKG/BK in `B_R`, uniformity in `R`,
      interior geometry, Schramm, `theta(p_c)=0`, bounds on `tau_(p_c)`) all
      survive the replacement. Such an argument dies at the integration step
      from `p_c` to `q>p_c` taken uniformly in `R`. The invariant it cannot
      see is the two-arm boundary probability, which is `0` at `p_c` and at
      least `theta(q)^2` above it.
    * *Gate.* A proof must use volume monotonicity
      (`P(x <-> y inside B_R) <= tau`) or block-chain confinement of pivotal
      edges at some `q>p_c`. Both known positive proofs (critical L2 and the
      cactus bound) use one of them.
    * *What the free boundary buys.* In the limit `R -> infinity` the
      free/wired gap equals `D_n(q)`, the probability that `o` and `X_n` lie
      in distinct infinite clusters. So (P2) forces
      `D_n(p) >= theta(p)^2 - (rho (p/p_c)^C)^n`. This refines the
      group-rings diagnosis "only finite ball truncation separates" to "only
      *free* truncation separates".
  * *Calibration on `T_3`.* The closed forms are checked by brute force. The
    maximum count per step on `[1/2,0.6]` is shown below.

    | `n` | free | wired, `R=10^5` |
    |---|---|---|
    | 10 | 0.211 | 1.008 |
    | 40 | 0.100 | 1.580 |
    | 60 | 0.078 | 2.462 |
    | 100 | 0.056 | 6.601 |
    | 140 | 0.044 | 18.901 |

    The maximiser moves toward `p_c` (`1.8e-4` at `n=140`).
  * *Verdict.* The target stays open. Any proof must enter through the gate.
* **Calibrate against amenable worlds (transplanter/calibration, b-p-bs3, swarm-0917).**
  * *Sandwich (rigorous, from established nodes).*
    - `fpbs-l2-gap-gives-bounded-pivotal-counts` gives `p_c<p_(2->2)` ⇒ PB.
    - `fpbs-pivotal-budget-implies-nonuniqueness` gives PB ⇒ `p_c<p_u`.
    - Hence a graph where PB fails has `p_c=p_(2->2)` and refutes Hutchcroft's
      critical-l2 conjecture (`fpbs-nonamenability-bounds-critical-connectivity-operator`).
    - PB is therefore no easier to *disprove* than that conjecture. By
      `fpbs-tree-walk-pivotal-count-bounded-below-l2-threshold`, it must be
      *proved* with genuinely linear counts.
  * *Where nonamenability enters (rigorous).* Integrating (1.1) gives
    `int_c^p E_q[N_(n,R)|E_(n,R)] dq/q = log(a_(n,R)(p)/a_(n,R)(c))`.
    - On any transitive graph with uniqueness at `p`, the right side lies
      between `log(theta(p)^2/a_n(c)) - o_R(1)` and `log(1/a_(n,R)(c))`.
    - The only nonamenable input is Schramm's `a_n(c)<=rho^n`. It makes the
      integrated count at least `n log(1/rho) + 2 log theta(p)` under collapse.
    - Nothing in the hypothesis PB refers to `rho`. PB is a pivotal statement
      that could hold on amenable graphs, where `rho=1` and the theorem is
      silent.
    - Quantitatively, if PB holds with `(C,p0)` and `p0>p_u`, then
      `C >= log(1/rho)/log(p_u/p_c)`, because nonuniqueness is an interval
      ending at `p_u`. So as `rho -> 1`, the budget constant must blow up
      unless `p_u/p_c -> 1` at a comparable rate.
  * *Amenable calibration (heuristic only, not a result).*
    - On `Z^d` with `d>=11`, the lace-expansion two-point bound `|x|^(2-d)`
      gives `a_n(p_c) ≍ n^(-(d-2)/2)`. The integrated count is then `O(log n)`.
    - On `Z^2` at `p_c=1/2`, the four-arm exponent suggests `E[N|E]` is of
      order `min(|X_n|, L(p))^(3/4) <= n^(3/8)`.
    - Both suggest PB holds, far from saturated, on amenable graphs with
      `p_c=p_u`.
  * *Consequences for method choice.*
    - A disproof of PB must use a mechanism that does not operate on these
      amenable worlds. The only precise obstruction on record,
      `fpbs-hierarchical-pivotal-amplification`, is of that nontransitive,
      multiscale type.
    - A proof of PB may be amenability-blind, but it must then be sharp to
      within the linear order that trees show is necessary above
      `p_(2->2)`.
  * *Where it dies.*
    - No amenable transitive graph with `p_c<1` has a *rigorous* PB. The
      `Z^2` and `Z^d` numbers rest on unproved uniform-in-`R`
      near-critical pivotal bounds.
    - The heuristic therefore kills no class of approaches. It only
      calibrates that the budget, as stated, does not detect amenability.
    - The one rigorous price, `C >= log(1/rho)/log(p_u/p_c)`, is the
      contrapositive of the conditional theorem and adds no new constraint.
    - No new node was filed.
* **Make the parameter complex (reframing).**
  * *The idea.* `p (d/dp) log a_(n,R)` is a logarithmic derivative, so bound
    `log a_(n,R)` on a complex domain rather than its derivative on a real
    segment.
  * *What it proves (written, unrefereed; kept OPEN).* `fpbs-zero-free-connectivity-gives-flat-rate` (Harnack,
    Montel, identity theorem). Suppose the walk-averaged polynomials
    `a_(n,R)(z)` have no zeros (Z) and satisfy `|a_(n,R)| <= exp(Mn)` (G) on a
    simply connected domain meeting `(0,p_c]` and `(p_c,1)`, uniformly in
    `n>=n_0` and `R>=n`. Then:
    - `lambda=rho` on the interval past `p_c`, so `p_c<p_u`;
    - this budget holds on compact intervals away from `p_c`.
  * *How it relates to this hole.* It is a separate decomposition of the goal
    (`fpbs-zero-free-connectivity-route`, open hypothesis
    `fpbs-connectivity-polynomials-zero-free-around-criticality`), and neither
    implies the other. It yields no budget on `[p_c,p_0]` itself, and it forces
    a flat rate where this claim gives only a Lipschitz one.
  * *Where it can die.*
    - (N2) a fixed-`n` singularity of `a_n` at `p_c`;
    - (N3) the growth step (G) as `R -> infinity`.
  * *Evidence.* `T_3` is numerically zero-free near `p_c` for `n<=200`, and
    (G) holds there with `M=0`. The parallel-routes toy grows without bound off
    the real axis. The first killing test is exact `a_(n,R)(z)` on a small
    Cayley graph with overlapping cycles as `R` grows
    (`research/artifacts/fpbs-zero-free-connectivity-2026-09-17.md`).
