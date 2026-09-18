---
rg: 2
id: fpbs-two-point-fourier-algebra-criterion
kind: claim
title: The two-point function lies in the Fourier algebra iff its cluster form is closable; membership forces walk rate rho with constant one and nonuniqueness, the finite part and the critical state always lie in A, and the singular mass is at most theta
artifacts:
  - research/artifacts/fpbs/docs/fourier-algebra-two-point-2026-09-17.md
distinct_from:
  fpbs-all-parameter-finite-cluster-spectrum: that proves weak containment (walk correlations at most (1-theta) rho^n) of the finite-cluster part; this proves the finite-cluster part lies in the Fourier algebra A(Gamma) itself, and characterises A-membership of the full two-point function by closability of the cluster form
  fpbs-hp-thinning-two-point-exit: that uses weak containment of a thinned connectivity function in lambda as a necessary exit criterion; this is the strictly stronger Fourier-algebra membership, with an exact closability characterisation, for the Bernoulli two-point function
  fpbs-lq-two-point-bounds-walk-rate: that bounds the walk rate by rho^(2/q) from l^q summability; this gives the exact rate rho from A-membership, which is incomparable with l^q summability (Calibration 5.5 of the artifact)
  fpbs-two-point-state-axioms-admit-collapse: that kills the two-point state class; this adds A-membership at p_c and B-norm continuity to that class and shows the collapse witness still satisfies them
---

**ESTABLISHED.** Proof in `fpbs-two-point-fourier-algebra-criterion-proof`, and
in full in the artifact.

**Setting.**

- `Gamma` is nonamenable and finitely generated, `S` is finite symmetric
  generating, and `rho = ||lambda(mu_S)||`.
- `tau_p(x) = P_p(e <-> x)` for Bernoulli bond percolation, and `theta(p)` is
  the percolation density.
- `A(Gamma)` and `B(Gamma)` are the Fourier and Fourier–Stieltjes algebras.
- For `f` in `C_c(Gamma)` and a cluster `C`, put `f(C) = sum_(x in C) f(x)`.

**Theorem.**

1. *(Closability criterion.)* A real PD `phi` with `phi(e) = 1` is in
   `A(Gamma)^+`, that is `phi = <lambda(.) eta, eta>` with `eta` in `l^2`,
   if and only if the form
   `q_phi(f) = sum conj(f(x)) f(y) phi(x^(-1) y)` on `C_c` is closable in `l^2`.
   For `tau_p`, `q(f) = E_p sum_C |f(C)|^2`. PD `l^2` functions are in `A`
   (Friedrichs).
2. *(Consequences.)* If `tau_p` is in `A`, then:
   - `a_n(p) = sum_x mu^(*n)(x) tau_p(x) <= rho^n` for all `n`, so
     `lambda(p) = rho`;
   - `tau_p` is in `c_0`;
   - if `p > p_c`, then `p` is a nonuniqueness parameter, so `p_c < p_u`.
3. *(Finite part.)* For every `p`, `tau^fin_p(x) = P(e <-> x, |C| < infinity)`
   is in `A(Gamma)^+`. So `tau_p` is in `A` iff `tau^inf_p` is, and
   `dist_B(tau_p, A) <= theta(p)`. In particular `tau_(p_c)` is in `A` on
   every nonamenable Cayley graph.
4. *(Thresholds.)* Let
   `p_A = sup{p : tau_s in A for all s <= p}`. Then
   `p_c <= p_(2->2) <= p_2 <= p_A <= p_u`.
   On `d`-regular trees, `p_A = p_2 = (d-1)^(-1/2)`, which lies strictly
   between `p_c` and `p_u`.
5. *(Calibrations.)*
   - For `H` infinite amenable, `1_H` has walk rate `rho` but is not in `A`.
   - If `Gamma` has an element of infinite order, `A(Gamma)^+` contains
     functions in no `l^q` with `q < infinity`.
   - On trees, `l^q` contains `tau_p` outside `A`.
   - So `A`-membership and `l^q` summability are incomparable.
6. *(Class extension of the collapse kill.)* The collapse family `f_p` of
   `fpbs-two-point-state-axioms-admit-collapse` has `f_(p_c)` in `A` and
   `dist_B(f_p, A) <= theta(p)^2 -> 0`, yet `f_p` is in no `l^q` and not in
   `A` for every `p > p_c`. So no argument from (T1)–(T8) plus
   `A`-membership at `p_c` plus `B`-norm continuity proves `A`-membership or
   `l^q` summability at any `p > p_c`.

**Use.** Item 2 makes the OPEN hole
`fpbs-two-point-in-fourier-algebra-near-pc-universal` a sufficient condition for
(IS), and hence for BS. By item 6, that hole needs event-level input:
closability of the infinite-cluster form.
