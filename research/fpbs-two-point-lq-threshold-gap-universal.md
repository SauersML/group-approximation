---
rg: 2
id: fpbs-two-point-lq-threshold-gap-universal
kind: claim
title: On every nonamenable Cayley graph the two-point function stays l^q summable slightly above p_c for every q above 2
distinct_from:
  fpbs-nonamenability-bounds-critical-connectivity-operator: that asks for operator boundedness p_c < p_{2->2}, which implies this; this asks only that the single vector tau_p(o,.) lie in l^q for p slightly above p_c, for each q > 2, and it tolerates tau_p(o,.) not in l^2 for all p > p_c.
  fpbs-sphere-two-point-rate-right-continuous-universal: that asks the sphere-mass growth rate g(p) to vanish as p decreases to p_c; this controls sums of tau^q, which may converge while sphere masses grow exponentially, and the two hypotheses are incomparable a priori.
artifacts:
  - research/artifacts/fpbs/docs/lq-two-point-walk-rate-2026-09-17.md
---

**OPEN.** Let `G` be a nonamenable Cayley graph and set
`p_q = sup{p : sum_x tau_p(o,x)^q < infinity}`.

**[Q].** `p_c < p_q` for every `q > 2`.

**What it gives.** Combined with `fpbs-lq-two-point-bounds-walk-rate`,
`lambda(p) <= rho^(2/q)` just above `p_c` for every `q > 2`. Hence
`lambda(p) -> rho`, which is (IS) (route
`fpbs-integrated-sensitivity-via-lq-two-point`).

**Known cases.**

- Every class with `p_c < p_{2->2}`, since `p_{2->2} <= p_2 <= p_q`.
- Regular trees, where `p_q = (d-1)^(-1/q) > 1/(d-1)`.

**Failure mode.** [Q] fails iff some `q_0 > 2` has
`inf{q : Z_q(p) < infinity} >= q_0` for every `p > p_c`. Section 6 of the
artifact shows that a failure of [Q] would not by itself refute (IS).

## Attempts

* **Russo-BK openness (swarm-0917-w5).** The derivative of `Z_q` is majorized
  by a mixed `(q-1,1,1)` convolution sum.
  **Where it dies:** closing it needs a triangle or operator bound. That bound
  is infinite above `p_c` (`chi_p = infinity`). This is the obstruction of
  `fpbs-bk-majorant-integrated-sensitivity-is-critical-l2`.
* **Critical import.** Take `Z_q(p_c) < infinity` from critical decay.
  **Where it dies:** arXiv:1605.05301v1, thm:pcconnectivitydecay, bounds only
  the infimum `kappa_{p_c}(n)`, not typical `tau_{p_c}(o,x)`. It would also
  still leave openness through `p_c`. See Section 7 of the artifact.
* **Operator-algebra transplant: Fourier algebra and noncommutative L^r
  (swarm-0917-w7).**
  - *Proved* (`fpbs-two-point-fourier-algebra-criterion`, established):
    - `tau_p` is in `A(Gamma)` iff the cluster form
      `f -> E sum_C |f(C)|^2` is closable in `l^2`;
    - `A`-membership gives `a_n <= rho^n` with constant one, and
      nonuniqueness if `p > p_c`;
    - `tau^fin_p` is always in `A`, `tau_(p_c)` is in `A`, and
      `dist_B(tau_p, A) <= theta(p) -> 0`.
  - *Where it dies for [Q]:* at the step from `B`-norm information at `p_c` to
    `l^q` summability above it.
    - `l^q` is neither `B`-closed nor `B`-open.
    - `A`-membership carries no summability exponent: `A(Gamma)^+` contains
      functions in no `l^q` whenever `Gamma` has an element of infinite order.
    - The collapse witness `f_p` of `fpbs-two-point-state-axioms-admit-collapse`
      satisfies `f_(p_c)` in `A` and `dist_B(f_p, A) <= theta^2 -> 0`, yet it is
      in no `l^q` for `p > p_c`.
    - Noncommutative Hausdorff–Young (`T_p` in `L^r(L Gamma)` with `r < 2`
      gives `tau` in `l^(r')`) needs the same unavailable critical input.
  - *What it gives instead:* an incomparable sibling hole [A],
    `fpbs-two-point-in-fourier-algebra-near-pc-universal`. It also implies (IS)
    and BS (route
    `fpbs-integrated-sensitivity-via-fourier-algebra-two-point`).
  - *Calibration:* on trees both holes hold, and `p_A = p_2` lies strictly
    below `p_q` and `p_u`.
