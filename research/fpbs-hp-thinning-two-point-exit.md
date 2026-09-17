---
rg: 2
id: fpbs-hp-thinning-two-point-exit
kind: claim
title: Cluster-coin thinning stays in the Bernoulli closure only if its connectivity function is weakly contained in the regular representation, so the Hutchcroft--Pete scheme in W_b condenses only at disagreement at least 2(1-rho)p r(p)
artifacts:
  - experiments/hp-thinning-two-point-2026-09-17/recursion_check.py
  - experiments/hp-thinning-two-point-2026-09-17/output.txt
distinct_from:
  fpbs-hp-condensation-bernoulli-exit: that proves the exit dichotomy (frequency stage or non-hyperfinite stage) and an exit bound at average disagreement 2(1-rho)p(1-p); this gives the exact two-point exit criterion tau_E weakly contained in lambda for any coin subrelation, the exact group-independent disagreement recursion of the scheme, and the resulting obstruction to disagreement-threshold condensation certificates.
  fpbs-kazhdan-ergodic-percolation-disagreement-floor: that is a lower bound on disagreement for ergodic percolation from a Kazhdan pair; here the lower bound comes from staying inside W_b and is compared with such floors to show when they cannot certify alternative (I).
  fpbs-kazhdan-local-cost-formula: that derives condensation from a window defect below kappa^2 p; this shows the window-0 instance of that certificate cannot fire along the Hutchcroft--Pete scheme inside W_b unless kappa(S)^2 > 2(1-rho(S)) r(p).
---

**ESTABLISHED (obstruction; written proof in the proof route, exact recursion checked by Monte Carlo, free-group
calibration checked numerically).**

**Setting.** As in `fpbs-hp-condensation-bernoulli-exit`.
- `Gamma` is finitely generated, `S` a finite symmetric generating set, `m` uniform on `S`, `rho = ||lambda(m)||`.
- `mu` is an invariant site percolation on `{0,1}^Gamma`, with clusters taken in `Cay(Gamma,S)` and marginal `p`.
- `W_b` is the weak-star closed class of percolations `mu` with `s_mu x b ≺ b`.
- `u = sqrt(1-p)`, `q = 1/(1+u) = (1-sqrt(1-p))/p`, and `mu_i` is the Hutchcroft--Pete recursion. `i_*(p)` is the
  first `i` with `mu_i^q` not in `W_b`, and `i_freq(p)` the first stage with a positive-frequency cluster.
- Let `E` be an invariant Borel subrelation of the cluster relation of `mu x b` ("coin classes"). `mu^{q,E}` retains
  each `E`-class independently with probability `q`. Its *connectivity function* is
  `tau_E(g) = P(omega(e) = omega(g) = 1 and e ~_E g)`. For `E` the full cluster relation, write `tau` and `mu^q`.
- `D_i(s) = mu_i(omega(e) != omega(s))`.

**Theorem.**
- **(T1) Two-point exit criterion.** `tau_E` is positive definite, and
  `Cov_{mu^{q,E}}(e,g) = q^2 Cov_mu(e,g) + q(1-q) tau_E(g)`. If `mu^{q,E}` is in `W_b`, then the GNS representation
  of `tau_E` is weakly contained in `lambda`. Hence `|sum_g c(g) tau_E(g)| <= ||lambda(c)|| p` for every finitely
  supported `c`. In particular, for simple random walk `X_n` independent of `omega`,
  `P(e and X_n are occupied and E-related) <= rho^n p` for all `n`.
- **(T2) Exact recursion.** For every group, every `S` and every `s` in `S`, `D_i(s) = D_i`, where
  `D_1 = 2p(1-p)` and `D_{i+1} = q D_i (2u - q D_i/2)`. The sequence decreases, with
  `r(p) D_i <= D_{i+1} <= (2u/(1+u)) D_i` and `r(p) = q(2u - q p(1-p)) = 1 - p/2 + O(p^2)`.
- **(T3) Explicit exit bound.** `i_*(p) <= i_0(p,rho) = min{i : D_i < 2(1-rho) p}`, so
  `i_*(p) <= 2 + max(0, log((1-p)/(1-rho)) / log((1+u)/(2u)))`, which is about `(4/p) log(1/(1-rho))` for small
  `p`. The bound depends on `Gamma` and `S` only through `rho`.
- **(T4) Disagreement at condensation.** Every stage `2 <= j <= i_*(p)` has `D_j >= 2(1-rho) p r(p)`, and
  `D_1 = 2p(1-p)`. In alternative (I) of `fpbs-hp-condensation-bernoulli-exit` the condensing stage is
  `j = i_freq = i_*`, so it has this disagreement.

**Obstruction (class-killing for disagreement certificates).** Call a *disagreement certificate with constant `c`*
any theorem of the form "an invariant percolation of marginal `p` in the relevant class with
`max_s D(s) < c p` has a positive-frequency cluster". To certify alternative (I) along the scheme, a certificate must
fire at some stage `j <= i_*`. Since `D_j(s)` does not depend on `s`:
- At `j = 1` it needs `c > 2(1-p)`. For `p < p_c(Cay(Gamma,S))` stage 1 has only finite clusters, so it is not
  available.
- At `2 <= j <= i_*` it needs `c > 2(1-rho) r(p)`, by (T4).
- Hence for `p < p_c`, no disagreement certificate with `c <= 2(1-rho(S)) r(p)` can certify alternative (I).

**Kazhdan instances.**
- The window-0 case of Theorem 1 of `fpbs-kazhdan-local-cost-formula` has `c = kappa(S)^2`.
- Any certificate obtained by contradicting the floor of `fpbs-kazhdan-ergodic-percolation-disagreement-floor` has
  `c = kappa(S)^2 (1-p)`, which is smaller.
- Neither can certify alternative (I) at any `p < p_c` with `kappa(S)^2 <= 2(1-rho(S)) r(p)`.
- Since `r(p) -> 1` as `p -> 0`, neither can certify it at any small `p` for a Kazhdan pair with
  `kappa(S)^2 < 2(1-rho(S))`.

**Averaged form.** Let `eps(S) = 1 - sup{max spec pi(m) : pi unitary without invariant vectors}`. The averaged
Kazhdan inequality gives `sum_s m(s) D(s) >= 2 eps(S) p(1-p)` for ergodic percolation, so the averaged certificate
constant is `c = 2 eps(S)`. It is at most `2(1-rho)`, because `lambda` is such a `pi` and `max spec lambda(m) = rho`.
So for `p < p_c` the averaged certificate cannot certify (I) whenever `r(p) >= eps(S)/(1-rho(S))`. This holds for all
small `p` as soon as some unitary representation without invariant vectors (for instance `l^2_0` of a finite
quotient) has top spectrum strictly above `rho`.

Therefore any proof of fixed price one for Kazhdan groups through the Hutchcroft--Pete scheme inside `W_b` needs a
condensation mechanism at neighbour disagreement at least `2(1-rho)p r(p)`, close to the maximal possible `2p`. That
means window-`R > 0` statistics, or a non-spectral input, which cannot be reduced to neighbour disagreement.

**Calibration.**
- **Amenable groups.** `rho = 1`, so (T1), (T3) and (T4) are vacuous, as they must be.
- **Free groups.** For `F_r` with standard generators, stage 1 is Bernoulli(`p`) site percolation, with
  `tau(g) = p^{|g|+1}`. By the Haagerup inequality, (T1) fails exactly when `p > 1/sqrt(2r-1)`. So exact cluster
  thinning leaves `W_b` already at stage 1 for those `p`, which is consistent with alternative (II) being forced
  there.
  - Numerically, the rate of `sum_g m^{*n}(g) tau(g) = p E[p^{|X_n|}]` is `rho` for `p <= 1/sqrt(2r-1)` and the
    spherical value `(1/p + (2r-1)p)/(2r) > rho` above it (`r = 2, 3`, `n = 4000`).
  - Below the threshold, criterion (T1) does not decide membership: it is only necessary.
- **The recursion (T2)** is group-independent. It was checked by Monte Carlo on the `32 x 32` torus at `p = 0.3`,
  stages 1--4, 300 trials, all within 1.4 standard errors. See
  `experiments/hp-thinning-two-point-2026-09-17/output.txt`.

**What this does not do.**
- (T1) is necessary, not sufficient, for staying in `W_b`.
- (T4) constrains certificates, not alternative (I) itself: `i_freq <= i_*` is still possible, with condensation
  forced by something other than small neighbour disagreement.
