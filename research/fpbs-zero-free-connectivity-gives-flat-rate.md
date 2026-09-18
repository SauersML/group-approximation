---
rg: 2
id: fpbs-zero-free-connectivity-gives-flat-rate
kind: claim
title: Zero-free bounded connection polynomials around criticality give a flat walk rate past p_c and p_c<p_u
distinct_from:
  fpbs-pivotal-budget-implies-nonuniqueness: that assumes a real-variable linear pivotal budget on [p_c,p_0] and gets only a Lipschitz rate; this assumes a complex zero-free region with exponential growth control that may avoid p_c, and gets a flat rate lambda=rho on an interval past p_c
  fpbs-l2-gap-gives-bounded-pivotal-counts: that assumes the operator gap p_c<p_(2->2) and bounds the pivotal count independently of n; this assumes no operator bound, only zeros and growth of the finite connection polynomials
artifacts:
  - research/artifacts/fpbs-zero-free-connectivity-gives-flat-rate-proof-attempt-2026-09-17.md
  - research/artifacts/fpbs-zero-free-connectivity-2026-09-17.md
---

Let `G` be a nonamenable Cayley graph, `X_n` simple random walk from `o`,
`a_(n,R)(z)` the walk-averaged connection polynomial of the ball `B_R`, and
`rho=||P||`. Suppose that there are a simply connected domain `U` in `C`,
open intervals `I_-` in `(0,p_c]` and `I_+` in `(p_c,1)` contained in `U`,
and constants `M`, `n_0` such that for all `n>=n_0` and `R>=n`:

- (Z) `a_(n,R)` has no zero in `U`;
- (G) `|a_(n,R)(z)| <= exp(M n)` on `U`.

Then:

- (a) `lambda(p)=lim_n a_n(p)^(1/n)=rho` for every `p` in `I_+`;
- (b) every `p` in `I_+` is in the nonuniqueness phase, so `p_c<p_u`;
- (c) on each compact `J` in `I_- union I_+`,
  `E_p[N_(n,R)|E_(n,R)] <= C_J n` uniformly in `n>=n_0` and `R>=n`.

`U` need not contain `p_c`.

## Attempts

1. **Harnack and Montel bounds on log a_(n,R), then the identity theorem carries lambda=rho around p_c (2026-09-17).**
   Formerly the route `fpbs-zero-free-connectivity-gives-flat-rate-proof` (requires
   `fpbs-integrated-pivotal-rate-identity`); see
   `research/artifacts/fpbs-zero-free-connectivity-gives-flat-rate-proof-attempt-2026-09-17.md` and Section 2 of
   `research/artifacts/fpbs-zero-free-connectivity-2026-09-17.md`. Kept OPEN at salvage: the lane was cut off
   before any referee pass, so this written proof is unrefereed. No error has been reported.
