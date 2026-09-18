---
rg: 2
id: fpbs-two-point-fourier-algebra-criterion-proof
kind: route
title: Represent the closed cluster form by a positive operator commuting with the left regular representation, take eta as its square root at the identity, and truncate by cluster size to put the finite part in the closed ideal A
target: fpbs-two-point-fourier-algebra-criterion
requires:
  - fpbs-critical-no-infinite-cluster
  - fpbs-lq-two-point-bounds-walk-rate
  - fpbs-two-point-state-axioms-admit-collapse
artifacts:
  - research/artifacts/fpbs/docs/fourier-algebra-two-point-2026-09-17.md
---

Section numbers refer to the artifact.

1. **Cluster form (Lemma 1.1).** Expand `|f(C)|^2` over clusters and use
   invariance. This gives `q_(tau_p)(f) = E sum_C |f(C)|^2`, and the same for
   finite clusters and for infinite clusters. So all three kernels are PD.
2. **(b) => (a) (Theorem 2.1).**
   - `q_phi(f) = ||f * eta||^2`.
   - `f -> f * eta` has densely defined adjoint `h -> h * eta~`, so it is
     closable, and so is the form.
3. **(a) => (b) (Theorem 2.1).**
   - Kato's representation theorems give a positive self-adjoint `T` with
     `qbar = ||T^(1/2) .||^2`.
   - Left-translation invariance and uniqueness make `T` commute with
     `lambda(Gamma)`, so `T^(1/2)` is affiliated with `R(Gamma)`.
   - Then `eta = T^(1/2) delta_e` satisfies `phi(g) = <lambda(g) eta, eta>`.
4. **l^2 => A (Corollary 2.2).** The form of the nonnegative symmetric operator
   `f -> f * phi` is closable (Friedrichs).
5. **Consequences (Theorem 3.1).**
   - `a_n = <lambda(mu)^n eta, eta> <= rho^n`, and Lemma 2.2 of
     `fpbs-lq-two-point-bounds-walk-rate` gives `lambda >= rho`.
   - Coefficients of `l^2` vectors are `c_0`, by finite-support approximation.
   - Uniqueness at `p > p_c` would force `tau_p >= theta^2` (Harris–FKG).
     Monotonicity of uniqueness then gives `p_c < p <= p_u`.
6. **Finite part (Proposition 4.1).**
   - The size-truncated kernels `phi_R` are finitely supported and PD, hence in
     `A`.
   - The error `tau^fin - phi_R` is PD with `B`-norm
     `P(R < |C| < infinity) -> 0`.
   - `A` is a closed ideal of `B` (Eymard).
   - `theta(p_c) = 0` (`fpbs-critical-no-infinite-cluster`) puts `tau_(p_c)` in
     `A`.
7. **Thresholds and calibrations (Section 5).**
   - Item 4 gives `p_2 <= p_A`, and item 5 gives `p_A <= p_u`.
   - Trees use the walk-rate computation in Section 5 of
     `research/artifacts/fpbs/docs/lq-two-point-walk-rate-2026-09-17.md`.
   - The slow-decay element uses the convexity theorem on `Z` (Zygmund V.1.5),
     extended by zero from a cyclic subgroup.
8. **Class extension (Section 6).**
   - `f_p - (1 - theta^2) tau_(p_c) = theta^2`, which has `B`-norm `theta^2`,
     and `tau_(p_c)` is in `A` by item 6.
   - `f_p >= theta^2 > 0` is not in `c_0`, so it is not in `A` and in no `l^q`.
   - (T1)–(T8) come from `fpbs-two-point-state-axioms-admit-collapse`.
