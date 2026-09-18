---
rg: 2
id: fpbs-hp-thinning-two-point-exit-proof
kind: route
title: Radon--Nikodym domination of the thinned covariance, an exact two-point recursion, and a monotone ratio bound give the thinning exit criterion and the disagreement obstruction
target: fpbs-hp-thinning-two-point-exit
requires:
  - fpbs-hp-condensation-bernoulli-exit
---

Full written proof. The notation is that of the target node.

**Imported inputs.**
- Weak containment of actions passes to Koopman representations on `L^2_0` (Kechris, *Global aspects of ergodic
  group actions*, Prop. 10.5). The Koopman representation of `b` on `L^2_0` is a multiple of `lambda`.
- Radon--Nikodym for positive definite functions (Dixmier, *C\*-algebras*, 2.5.1). If `psi` and `phi - psi` are
  positive definite, then `psi(g) = <pi_phi(g) T xi_phi, xi_phi>` for some `T` in the commutant of `pi_phi` with
  `0 <= T <= 1`.
- Kesten: `lambda(m)` is self-adjoint, `||lambda(m)|| = rho = max spec lambda(m)`, and `rho < 1` iff `Gamma` is
  nonamenable.
- Haagerup's inequality on `F_r`: `||lambda(f)|| <= (n+1) ||f||_2` for `f` supported on the sphere `S_n`.

## 1. Proof of (T1)

Let `xi = mu^{q,E}`, `xi(g) = omega(g) kappa([g]_E)`, where the coins `kappa` are i.i.d. Bernoulli(`q`) on `E`-classes
and independent of `(omega, b)`.

**Covariance identity.** Two occupied sites in the same `E`-class share one coin. Otherwise the coins are independent.
So
`E[xi(e) xi(g)] = q^2 E[omega(e) omega(g)] + (q - q^2) tau_E(g)`.
Since `E xi(e) = qp`, this gives `Cov_xi(e,g) = q^2 Cov_mu(e,g) + q(1-q) tau_E(g)`.

**Positive definiteness.**
- `Cov_mu` is positive definite, being the covariance of a stationary field.
- For `tau_E`, take points `x_1..x_k` and complex `c_i`. By invariance, `tau_E(x_i^{-1} x_j)` is the probability that
  `x_i` and `x_j` are occupied and `E`-related. Then
  `sum_{i,j} c_i conj(c_j) tau_E(x_i^{-1} x_j) = E sum_C |sum_{x_i in C} c_i|^2 >= 0`,
  where `C` ranges over `E`-classes.

**Weak containment.** Suppose `xi` is in `W_b`, so `s_xi x b ≺ b`.
- The function `Cov_xi` is the coefficient of `f = 1_{xi(e)=1} - qp` in `L^2_0(xi x b)`. So its GNS representation is a
  subrepresentation of the Koopman representation on `L^2_0`, which is `≺ b` on `L^2_0`, that is `≺ lambda`.
- Apply Radon--Nikodym with `phi = Cov_xi` and `psi = q(1-q) tau_E`. Both `psi` and `phi - psi = q^2 Cov_mu` are
  positive definite. So `tau_E` is a vector coefficient of `pi_phi`, and `pi_{tau_E}` is a subrepresentation of
  `pi_phi ≺ lambda`.

**Consequences.**
- For finitely supported `c`, `|sum_g c(g) tau_E(g)| <= ||pi_{tau_E}(c)|| tau_E(e) <= ||lambda(c)|| p`, since
  `tau_E(e) = p`.
- With `c = m^{*n}` and `lambda(m)` self-adjoint, `P(e and X_n are occupied and E-related) <= rho^n p`.
- **Neighbour form.** For `s` in `S`, occupied neighbours lie in one cluster. So for `E` the full cluster relation,
  `tau(s) = P(omega(e) = omega(s) = 1) = p - D(s)/2`. Taking `n = 1` gives `p - mean_s D(s)/2 <= rho p`, that is
  `mean_s D(s) >= 2(1-rho) p`. (1.1)

## 2. Proof of (T2)

Fix `s` in `S` and a stage with `D = mu_i(omega(e) != omega(s))`, marginal `p`, and `u = sqrt(1-p)`.
- **Thinning.** `X = mu_i^q` has marginal `qp = 1-u`. Occupied neighbours share a cluster, so they are kept together:
  `P_X(both occupied) = q(p - D/2)`. A site occupied with its neighbour vacant is kept with probability `q`, so
  `D_X = qD`. Then `P_X(both vacant) = 1 - 2(1-u) + q(p - D/2) = u - qD/2`.
- **Union.** `Z = X v X'` with `X, X'` independent copies. `P_Z(vacant) = u^2 = 1-p`, so the marginal is preserved,
  and `P_Z(both vacant) = (u - qD/2)^2`. So
  `D_Z = 2(P_Z(s vacant) - P_Z(both vacant)) = 2(u^2 - (u - qD/2)^2) = qD(2u - qD/2)`.
- **Group independence.** The recursion uses only the marginal and the neighbour two-point law, so `D_i(s)` is the
  same for every group, `S` and `s`, starting from `D_1 = 2p(1-p)`.

**Bounds.** Let `h(x) = qx(2u - qx/2)`.
- `h(x)/x = q(2u - qx/2)` is strictly decreasing, and `D_i > 0`. So `D_{i+1} < 2uq D_i = (2u/(1+u)) D_i < D_i`.
- Since `D_i <= D_1 = 2p(1-p)`, `D_{i+1}/D_i >= h(D_1)/D_1 = q(2u - q p(1-p)) = r(p)`.
- **Expansion.** `u = 1 - p/2 + O(p^2)` and `q = 1/2 + p/8 + O(p^2)`, so `2uq = 1 - p/4 + O(p^2)` and
  `q^2 p(1-p) = p/4 + O(p^2)`. Hence `r(p) = 1 - p/2 + O(p^2)`.

## 3. Proof of (T3)

If `D_i < 2(1-rho)p`, then (1.1) fails for `mu_i`, so `mu_i^q` is not in `W_b` and `i_* <= i`. Hence `i_* <= i_0`.
- For `i >= 2`, by Section 2, `D_i < (2u/(1+u))^{i-1} 2p(1-p)`.
- This is `<= 2(1-rho)p` as soon as `i - 1 >= L = log((1-p)/(1-rho)) / log((1+u)/(2u))`.
- So `i_0 <= max(2, ceil(L) + 1) <= 2 + max(0, L)`.
- Since `log((1+u)/(2u)) = p/4 + O(p^2)`, `L = (4/p) log(1/(1-rho)) (1 + O(p))`.

## 4. Proof of (T4) and the obstruction

**(T4).** Let `2 <= j <= i_*`. Then `j - 1 < i_*`, so `mu_{j-1}^q` is in `W_b`, and (1.1) gives `D_{j-1} >= 2(1-rho)p`.
By Section 2, `D_j >= r(p) D_{j-1} >= 2(1-rho) p r(p)`.

**Obstruction.** A certificate proving alternative (I) along the scheme must produce a positive-frequency cluster at
some stage `j <= i_*`, so it must fire there, which needs `max_s D_j(s) < cp`.
- For `p < p_c` the stage-1 clusters are finite, so they have zero frequency on the infinite group `Gamma`. A valid
  certificate cannot fire at `j = 1`.
- At `2 <= j <= i_*`, (T4) and the `s`-independence of `D_j(s)` give `max_s D_j(s) >= 2(1-rho) p r(p)`, so firing
  needs `c > 2(1-rho) r(p)`.

**Kazhdan instances.** These are the constants `kappa^2` and `kappa^2 (1-p) <= kappa^2`, and they are handled by the
same inequality.

**Averaged form.**
- For ergodic percolation, `f = 1_{omega(e)=1} - p` is orthogonal to the invariant vectors of `L^2_0`. So
  `sum_s m(s) D(s) = 2 <(1 - pi(m)) f, f> >= 2 eps(S) p(1-p)`, which gives the constant `2 eps(S)`.
- `lambda` has no invariant vectors (`Gamma` is infinite) and `max spec lambda(m) = rho`, so `eps(S) <= 1 - rho`.
- If some representation without invariant vectors has top spectrum `> rho`, then `eps(S)/(1-rho) < 1`. Since
  `r(p) -> 1`, this gives the small-`p` statement.

## 5. Free-group calibration

Take `F_r` with the free generators and their inverses, and `mu_1 = Bernoulli(p)`. The geodesic from `e` to `g` is the
only path, so `tau(g) = p^{|g|+1}`.

**Necessity.** Suppose `tau ≺ lambda`. Apply Section 1 with `c = 1_{S_n}`, where `|S_n| = 2r(2r-1)^{n-1}`, together
with Haagerup's inequality:
`|S_n| p^{n+1} <= ||lambda(1_{S_n})|| p <= (n+1) |S_n|^{1/2} p`.
So `p^n |S_n|^{1/2} <= n+1` for all `n`, which forces `p <= 1/sqrt(2r-1)`. Hence for `p > 1/sqrt(2r-1)` (T1) fails,
and `mu_1^q` is not in `W_b`.

**Sufficiency of the necessary condition.** For `p < 1/sqrt(2r-1)`, `sum_n |S_n| p^{2n}` is finite, so `tau` is in
`l^2`. A positive definite `l^2` function is a coefficient of `lambda`, and at `p = 1/sqrt(2r-1)` Cowling--Haagerup--Howe
applies (`tau` is in `l^{2+eps}`). So (T1) holds, and it does not decide membership in `W_b`.

**Numerical rate.** `sum_g m^{*n}(g) tau(g) = p E[p^{|X_n|}]`. For `|x| >= 1`, `P p^{|x|} = gamma(p) p^{|x|}`, where
`gamma(p) = (1/p + (2r-1)p)/(2r)`, and `gamma(p) >= rho`, with equality iff `p = 1/sqrt(2r-1)` (AM--GM). The script
checks that the exponential rate is `rho` below the threshold and `gamma(p) > rho` above it, for `r = 2, 3`,
`n = 4000`.

## 6. Scope

- (T1) is only a necessary condition.
- (T4) bounds what small-disagreement certificates can do. It does not rule out `i_freq <= i_*`.
