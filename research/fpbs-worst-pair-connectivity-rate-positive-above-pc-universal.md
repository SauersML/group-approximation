---
rg: 2
id: fpbs-worst-pair-connectivity-rate-positive-above-pc-universal
kind: claim
title: On every nonamenable Cayley graph some p above p_c has a point in every large ball connected to the centre with exponentially small probability
distinct_from:
  fpbs-sphere-two-point-rate-below-arccosh-universal: that kernel (G) is a sphere-sum bound below arccosh(1/rho); this is a worst-pair bound, strictly weaker (it holds on the whole interval (p_c,1) of T_d, while (G) holds only below 1/sqrt(d-1))
  fpbs-sphere-two-point-rate-right-continuous-universal: that asks g(p) -> 0 at p_c+; this asks only one exponentially rare pair per radius at one p > p_c
  fpbs-intrinsic-growth-rate-positive-at-pu: that is a positive chemical-radius rate at p_u; this is a positive extrinsic worst-pair decay rate just above p_c
artifacts:
  - research/artifacts/fpbs/docs/benjamini-schramm-frontier-map.md
---

**OPEN (kernel K).** Let `G` be a Cayley graph of a finitely generated
nonamenable group. Then some `p > p_c` and some `c > 0` satisfy, for infinitely
many `n`,

```text
min_(v in B_n) tau_p(o,v)  <=  e^(-cn).
```

Since `-(1/n) log kappa_p(n)` converges (item 1 of
`fpbs-worst-pair-connectivity-rate-kernel`), this is exactly `gamma(p) > 0`.

**What it gives.** `p_c < p_u`, by item 4 of
`fpbs-worst-pair-connectivity-rate-kernel`. The kernels (EG), (G) and (K')
each imply (K).

**Position.**

- **Converse.** `p_c < p_u` gives `kappa_p(n) -> 0` for `p in (p_c,p_u)`, via
  Lyons–Schramm indistinguishability (recalled, not imported), but not an
  exponential rate. So (K) is at most one "exponential versus subexponential
  decay in the nonuniqueness phase" step from the flagship statement.
- **Where a collapse must live: a jump of size at least log gr.** Hutchcroft
  arXiv:1605.05301v1, Theorem 2, as transcribed in Section (c) of the artifact:
  `kappa_(p_c)(n) <= gr^(-n)`. That gives `gamma(p_c) >= log gr`, recalled
  here and not load-bearing. So (K) fails exactly when the left-continuous
  function `gamma` drops from at least `log gr` at `p_c` to `0` on
  `(p_c,1]`. On `T_d`, `gamma(p) = -log p` is continuous.
- **The class that cannot prove it.** By item 6, no finite-radius
  certificate at `p_c` or above bounds `gamma` from below. Unlike Simon–Lieb
  (submultiplicative, where one radius suffices), `kappa` is
  *super*multiplicative. So a proof must control every radius at once, in
  the same way that `kappa_p(n) |B_n| <= chi_p` does for `p < p_c`.
- **The supercritical substitute that is missing.** Split
  `tau_p(o,v) = P_p(o <-> v, |K_o| < infinity) + P_p(o <-> v, |K_o| = infinity)`.
  Summing over `B_n`, (K) follows from these two statements at one `p > p_c`:
  - (a) `E_p[|K_o ∩ B_n| ; |K_o| = infinity] <= e^((log gr - c)n)`: infinite
    clusters have expected extrinsic growth strictly below `gr`;
  - (b) `E_p[|K_o| ; |K_o| < infinity] = e^(o(n))`, where the left side is the
    finite-cluster susceptibility, or merely its ball truncation.

  Each of (a) and (b) can fail, and neither is in the graph.

## Attempts

1. **Conditional chemical slope at the critical worst pairs
   (2026-09-18, swarm-0917-w7-w7-bs-follow).**
   - **Established:** `fpbs-worst-pair-critical-rate-and-chemical-slope-tradeoff`.
     - It proves `kappa_(p_c)(n) <= gr^(-n)` from subcritical sharpness
       alone, by Fekete and lower semicontinuity. So `gamma(p_c) >= log gr`
       is now load-bearing, not merely recalled.
     - It proves `gamma(t) + l(t) log(t/p_c) >= gamma(p_c)` for all
       `t > p_c`. Here `l(t)` is the conditional chemical slope of the
       `p_c`-minimisers.
     - The inequality is an equality on `T_d` at every `t`.
   - **New route:** `fpbs-worst-pair-rate-via-chemical-slope`, through the OPEN
     kernel (CS), `fpbs-worst-pair-chemical-slope-below-threshold-universal`.
   - **Obstruction:** a collapse forces `l(p_c+epsilon) >= p_c log(gr)/epsilon`.
     Every unconditional stretch or short-path construction is capped at the
     same threshold (tradeoff item 5), so it cannot prove (CS).
   - **Correction to the Position section:** input (b) of the (a)/(b) split
     is already in the graph. `fpbs-supercritical-finite-susceptibility`
     (Hermon–Hutchcroft, via `fpbs-hermon-hutchcroft-finite-tail-input`) gives
     `E_p[|K_o|; |K_o| < infinity] < infinity` for every `p > p_c`. So the
     split needs only (a), which is a ball form of (K').

2. **Worst-pair Russo budget against uniqueness-phase bridge bounds
   (2026-09-18, swarm-0917-w8-w8-bs-follow; OPEN, nothing closed).**
   - **The (a)/(b) split is not a decomposition. It dies as circular.**
     - `E_p|K_o ∩ B_n| = sum_(v in B_n) tau_p(o,v)` splits into a
       finite-cluster part and part (a). The finite-cluster part is at most
       `chi_f(p) < infinity` by Hermon–Hutchcroft.
     - So, given (b), (a) at rate `c` is equivalent to
       `E_p|K_o ∩ B_n| <= e^((log gr - c)n + O(1))`. This is the statement
       `g(p) < log gr`, because the ball and sphere sums have the same
       exponential rate. That statement is (K') itself.
     - Therefore "only (a) remains" means "(K') remains", and (K') ⟹ (K) is
       already item 4 of `fpbs-worst-pair-connectivity-rate-kernel`. The
       split adds no prerequisite that can fail on its own.
   - **Established here: under collapse, the worst-pair budget is spent in
     exponentially thin windows, as exponential pivotal spikes at deterministic
     endpoints.**
     - *Setting.* Suppose `p_c = p_u`. Fix `alpha in (0, (log gr)/2)` and let
       `v_n in A_n` be a critical worst pair, so `tau_(p_c)(o,v_n) <= gr^(-n)`
       (tradeoff item 1). Put `s_n = p_c + e^(-alpha n)`.
     - *Lower bound at `s_n`.* Uniqueness at `s_n` gives
       `tau_(s_n)(o,v_n) >= theta(s_n)^2`, by item 2 of the kernel claim. The
       linear lower bound `theta(p_c+epsilon) >= K epsilon`
       (`fpbs-transitive-sharpness-linear-lower-bound`) then gives
       `tau_(s_n)(o,v_n) >= K^2 e^(-2 alpha n)`.
     - *Passing to a finite ball.* `P(o <-> v inside B_R)` increases to `tau`
       as `R` grows. So some `R_n >= n` has
       `tau^(R_n)_(s_n)(o,v_n) >= K^2 e^(-2 alpha n)/2`. Also
       `tau^(R_n)_(p_c) <= tau_(p_c) <= gr^(-n)`.
     - *Russo and the mean value.* Russo's identity for the polynomial
       `tau^(R_n)` is exact. The mean-value inequality then gives some
       `q_n in (p_c, s_n)` with

       ```text
       E_(q_n)[ N^(R_n)(o,v_n) | o <-> v_n inside B_(R_n) ]
           >=  ( (log gr - 2 alpha) n + log(K^2/2) ) / log(s_n/p_c)
           >=  p_c ( (log gr - 2 alpha) n - O(1) ) e^(alpha n) .
       ```

     - *Comparison with `fpbs-collapse-exponential-pivotal-spikes`.* That
       claim has walk-averaged endpoints and exponent
       `lambda_0 = log(1/rho)`. This version has deterministic endpoints and
       the larger exponent `log gr`. It is larger because
       `log(1/rho) <= arccosh(1/rho) <= log gr`, and the range of `alpha`
       roughly doubles on trees.
     - *Status.* This is a necessary condition under collapse, not a
       contradiction. It is recorded here and not as a new claim.
   - **Obstruction: bounds taken at a fixed q and uniform in the endpoint
     cannot see the spikes.** Call `B` an *endpoint-uniform majorant* on
     `(s,t]` if, for all `v` and all `s < s' < t' <= t`,

     ```text
     log tau_(t')(o,v) - log tau_(s')(o,v) <= int_(s')^(t') B(q) dq/q .
     ```

     A bound `sup_(v,R) E_q[N^R | o <-> v inside B_R] <= B(q)` gives such a
     majorant by letting `R` go to infinity. This is the form that
     `fpbs-global-pivotal-tail-at-uniqueness` and
     `fpbs-uniqueness-pivotals-are-dangling-bridges` would take.
     - *Claim (proved here).* If `t` is a uniqueness parameter, then every
       endpoint-uniform majorant on `(p_c,t]` has

       ```text
       int_s^t B dq/q >= 2 log( theta(t)/theta(s) )   for every s in (p_c,t),
       ```

       and so `int_(p_c)^t B dq/q = infinity`. This holds on every
       nonamenable Cayley graph, whether or not the thresholds collapse.
     - *Proof.* Take `s > p_c`.
       - The events `{o <-> S_R(o)}` and `{v <-> S_R(v)}` use disjoint edge
         sets once `d(o,v) > 2R+1`, so they are independent.
       - `P(d(o,v) <= |K_o| < infinity)` tends to `0`.
       - Together these give `limsup_(v -> infinity) tau_s(o,v) <= theta(s)^2`.
       - Uniqueness at `t` gives `tau_t(o,v) >= theta(t)^2`.
       - Finally, `theta` is right-continuous, being an infimum of increasing
         polynomials, and `theta(p_c) = 0` by
         `fpbs-critical-no-infinite-cluster`.
     - *Where the class dies.* Any majorant obtained from fixed-`q` structure
       of the uniqueness phase must already blow up at least like
       `2 d log theta`. So comparing such a majorant with the budget
       `n log gr` never produces a contradiction: the whole budget sits in
       windows `(p_c, p_c + e^(-alpha n))` whose position depends on `n`, and
       the spikes above live there.
     - *Consequence.* A proof of (K) through Russo must control how the
       conditional pivotal count at the worst pairs depends on `n` for
       `q - p_c` exponentially small in `n`. This is the same demand as the
       limit-order non-interchange of
       `fpbs-critical-pivotal-concentration-under-collapse`, now at the
       exponent `log gr`.
   - **Trivial corollary, noted so no one reclaims it.** Item 1 of the
     tradeoff claim, together with `kappa_p(n) >= p^n`, gives
     `p_c <= 1/gr`. This is already folklore from
     `chi_p >= |S_n| p^n` and sharpness.

3. **Boundary Radon–Nikodym tilt (2026-09-18, swarm-0917-w9-w9-bs-follow;
   OPEN, new decomposition and class kill).**
   - **Established:** `fpbs-boundary-tilted-susceptibility-kernel`.
     - Take any quasi-invariant probability `nu` on a `Gamma`-space, with
       cocycle `Delta_zeta(o,y) = d(y_* nu)/d nu (zeta)`. It carries
       Hutchcroft's tilted mass transport and the `lambda <-> 1-lambda`
       duality of `chi^nu_lambda = sum_y tau(o,y) int Delta^lambda d nu`,
       even though the Cayley group is unimodular.
     - If `chi^nu_(1/2)(p) < infinity` and the Radon–Nikodym growth `h_nu` is at
       least `h > 0` on a set of positive measure, then `gamma(p) >= h/2`. The
       proof is one line: pointwise summability at a good `zeta`.
   - **New route:** `fpbs-worst-pair-rate-via-boundary-half-tilt`, through the
     OPEN kernel [BT], `fpbs-boundary-half-tilt-above-pc-universal`, which asks
     for `p_c < p^nu_t`.
     - Its prerequisites fail independently: [BT] is false on every amenable
       graph (see below), while (K) is only asked on nonamenable ones.
     - [BT] sits below the l2 gap whenever `pi_nu ≺ lambda`, since then
       `p_(2->2) <= p^nu_t`.
   - **Calibration.**
     - On `T_d` with the visual measure, `p^nu_t = (d-1)^(-1/2)`. This matches
       Hutchcroft's end-fixing `p_t` and gives `gamma >= (1/2) log(d-1)`, which
       is sharp at the right endpoint.
     - Kernel (K) already holds, with `gamma >= (log gr)/2`, on hyperbolic,
       acylindrically hyperbolic and nonunimodular Cayley graphs. This follows
       from the two l2-gap nodes, `Z_2 <= ||T_p||^2` and item (C) of
       `fpbs-lq-two-point-infinite-cluster-reduction`. So what remains open in
       (K) lies outside these classes.
   - **Class killed.** On `BS(1,2) x Z` acting affinely on `R` with the Cauchy
     law, every structural property holds:
     - the mass transport, the duality and convexity;
     - Radon–Nikodym growth at least `(log 2)/4` at every point;
     - weak containment and Zimmer-amenability.

     Yet `p^nu_t = p_c`. So no argument using only these properties and the
     amenability-blind inputs of the collapse calibration can prove [BT].
   - **Failing step.** A `zeta`-independent cocycle is trivial, so tilts are
     root-dependent. Hutchcroft's layer supermultiplicativity would then need
     fibre-uniform bounds, while mass transport gives only averages.
   - **Survivors.**
     - Harmonic or stationary `nu`, for example the Poisson boundary, whose
       stationarity the Cauchy example lacks.
     - Fibre-uniform estimates that fail on `BS(1,2) x Z`.
