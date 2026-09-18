---
rg: 2
id: fpbs-sublinear-zero-interpolant-iff-flat-rate
kind: claim
title: An analytic interpolant with sublinearly many zeros that dominates the walk connectivity at one supercritical point exists iff the walk rate is flat there, so every zero-free continuation hypothesis is exactly the flat-rate hole
distinct_from:
  fpbs-zero-free-connectivity-gives-flat-rate: that assumes the specific finite-volume polynomials a_(n,R) are zero-free and exponentially bounded for all n>=n_0 and R>=n, and proves the flat rate; this allows arbitrary analytic interpolants with o(n) zeros along a subsequence, dominating a_n at a single point, proves the converse, and shows linear zero counts are too weak
  fpbs-integrated-pivotal-rate-identity: that identifies integrated pivotal sensitivity with log(lambda/rho) in real parameter; this is a complex-analytic characterisation of lambda=rho at one supercritical point
  fpbs-two-point-fourier-algebra-criterion: that derives a_n<=rho^n from Fourier-algebra membership of tau_p; this derives it from analytic interpolation data, and characterises it
artifacts:
  - research/artifacts/fpbs-sublinear-zero-flat-rate-2026-09-18.md
  - experiments/fpbs-zero-count-flat-rate-2026-09-17/tree_zero_count_linear.py
---

**ESTABLISHED.** Proof in `fpbs-sublinear-zero-interpolant-iff-flat-rate-proof`.

**Setting.** `G` is a nonamenable Cayley graph, `X_n` simple random walk from
`o` independent of Bernoulli bond percolation, `a_n(p)=P_p(o <-> X_n)`,
`a_(n,R)` its version inside the ball `B_R`, `rho=||P||`, and
`lambda(p)=lim_n a_n(p)^(1/n)`.

**Theorem.** Let `p_+` be in `(p_c,1)`. The following are equivalent.

1. `lambda(p_+) = rho`.
2. `a_n(p_+) <= rho^n` for every `n>=1`.
3. There are a simply connected domain `U` with `conj(U)=U`, an open real
   interval `I` in `U` with `p_+` in `U`, an infinite set `S` of integers, and
   analytic functions `F_n` on `U` (`n` in `S`) such that, as `n -> infinity`
   in `S`:
   - (E) `|F_n|^(1/n) -> rho` uniformly on compact subsets of `I`;
   - (P) `a_n(p_+) <= e^(o(n)) |F_n(p_+)|`;
   - (G) for each compact `K` in `U` there is `M_K` with
     `sup_K |F_n| <= e^(M_K n)`;
   - (Z) for each compact `K` in `U`, `F_n` has `o(n)` zeros in `K`.

They imply that no `p <= p_+` has a unique infinite cluster, so
`p_c < p_+ <= p_u`, and every `p` in `(p_c,p_+]` has infinitely many infinite
clusters.

**Corollaries.**

- (C1) *Zero-free hypotheses are the flat-rate hole.* The implication 2 => 3
  is witnessed by the constant family `F_n = rho^n`, and also by the fixed-
  radius polynomials `F_n = a_(n,1)`, which have at most `|E(B_1)|` zeros. So
  any hypothesis of shape 3 that constrains the interpolants only through (E),
  (P), (G) and (Z) is equivalent to `lambda(p_+) = rho`. Complex analysis adds
  no information beyond the flat rate. A zero-free route gains only if it
  proves (Z) and (G) for polynomials that already capture `a_n(p_+)` up to
  `e^(o(n))`, that is for `a_(n,R)` at radii `R >= R_n(p_+)`, where
  `a_(n,R_n(p_+))(p_+) >= a_n(p_+)/2`.
- (C2) *Sublinear-zero ZG.* If the hypothesis (ZG) of
  `fpbs-connectivity-polynomials-zero-free-around-criticality` holds on a
  symmetric `U`, with (Z) weakened to `o(n)` zeros on compacts along a
  subsequence and (G) to local exponential bounds, then `lambda = rho` on
  every real point of `U` in `(p_c,1)`. Here (E) is automatic on
  `I` in `(0,p_c]` by Schramm's lemma and Kesten, for every `R>=1`.
- (C3) *Linear zero counts are too weak.* There is a family on a disc about
  `I` with (E), (G), exactly `n` zeros in a fixed compact, and
  `|F_n(p_+)|^(1/n) -> rho e^(g(p_+)) > rho` at each real `p_+` outside
  `closure(I)`. Here `g` is the Green function of `C` minus `closure(I)`. So
  `o(n)` in (Z) cannot be relaxed to `O(n)`.
- (C4) *Forced zeros.* If `lambda(p_+) > rho`, then every family with (E),
  (P) and (G) along all `n` has a compact `K` in `U` and `c>0` with at least
  `c n` zeros in `K` for all large `n`. On `T_d` this gives
  `fpbs-tree-connection-zeros-linear-past-flat-edge`.
