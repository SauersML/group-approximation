---
rg: 2
id: fpbs-flat-walk-rate-past-pc-universal
kind: claim
title: On every nonamenable Cayley graph the walk connectivity stays below rho^n at some supercritical parameter
distinct_from:
  fpbs-integrated-sensitivity-universal: that asks for right-continuity of lambda at p_c (lambda(p)->rho as p decreases to p_c); this asks for lambda(p_+)=rho exactly at some p_+>p_c, which is strictly stronger and is a single-parameter statement
  fpbs-two-point-lq-threshold-gap-universal: that asks for l^q summability of tau_p near p_c, which bounds a_n only by roughly rho^(2n/q); this asks for the flat bound a_n<=rho^n itself
  fpbs-two-point-in-fourier-algebra-near-pc-universal: that asks for tau_p in the Fourier algebra, which implies this hole by fpbs-two-point-fourier-algebra-criterion; whether the converse holds is unknown
  fpbs-connectivity-polynomials-zero-free-around-criticality: that is a complex zero-free hypothesis on the finite-volume polynomials, which implies this hole; by fpbs-sublinear-zero-interpolant-iff-flat-rate every interpolant-type zero-free hypothesis is equivalent to this hole, and ZG is stronger only by fixing the interpolants
---

**OPEN hole [F] (flat rate).**

**Statement.** Let `G` be a nonamenable Cayley graph, `X_n` simple random walk
from `o` independent of Bernoulli bond percolation, `a_n(p) = P_p(o <-> X_n)`
and `rho = ||P||`. There is `p_+ > p_c` with `a_n(p_+) <= rho^n` for every `n`,
equivalently `lambda(p_+) = rho`.

**Equivalent forms** (`fpbs-sublinear-zero-interpolant-iff-flat-rate`, established):

- `lambda(p_+) = rho` at one `p_+ > p_c`.
- `a_n(p_+) <= rho^n` for all `n` (supermultiplicativity and Fekete).
- There is an analytic interpolant with sublinearly many zeros that dominates
  `a_n(p_+)`, with `|F_n|^(1/n) -> rho` on a real interval (conditions
  (E), (P), (G), (Z) there).

Since `a_n` is monotone in `p`, the set `{p : lambda(p) = rho}` is an interval
`(0, p_F]`, and the hole says `p_F > p_c`.

**Consequences.**

- BS: `p_u >= p_F > p_c`, and there are infinitely many infinite clusters on
  `(p_c, p_F]`. See route `fpbs-flat-rate-route`.
- (IS), right-continuity of `lambda` at `p_c`, follows trivially.

**Implied by.**

- [A] Fourier-algebra membership of `tau_p` at some `p > p_c`. Route
  `fpbs-flat-rate-from-fourier-algebra`. Hence also by `p_c < p_2` and by
  `p_c < p_(2->2)`, which imply [A] by the chain in
  `fpbs-two-point-fourier-algebra-criterion`.
- (ZG). Route `fpbs-flat-rate-from-zero-free-polynomials`.

**Calibrations.**

- *Trees* (`fpbs-tree-connection-zeros-linear-past-flat-edge`, established).
  On `T_d`, `p_F = p_lambda = (d-1)^(-1/2) > p_c = 1/(d-1)`, and
  `p_F = p_2 = p_A` there. The hole holds, and it is sharp: `lambda = phi > rho`
  on `(p_F, 1)`, although nonuniqueness persists up to `p_u = 1`.
- *Unimodular random graphs.* The annealed analogue is false on the
  Angel--Hutchcroft graph `H~`: the annealed rate is at most `rho_bar` for
  `p <= p_c` and jumps to 1 for `p > p_c = p_u` (Theorem 2 of
  `fpbs-walk-rate-holes-fail-on-unimodular-random-graphs`). So any proof must
  use something Cayley-specific. One candidate input is supermultiplicativity
  `a_(n+m) >= a_n a_m`, which rests on left invariance and on the walk
  increments being independent, so it uses transitivity.
- *Strength.* `p_F <= p_u` always, and `p_F` can be strictly less than `p_u`
  (trees). The hole is implied by `p_c < p_2`; whether it is equivalent to it
  is unknown.

## Attempts

1. **Perturb the critical bound in real `p` (2026-09-18, swarm-0917-w8-w8-bs-last1). Deferred at a
   precise gap.**
   - Start from `a_n(p_c) <= rho^n` (`fpbs-critical-walk-correlation`) and integrate the finite Russo
     identity:
     `log a_(n,R)(p) - log a_(n,R)(p_c) = int_(p_c)^p E_q[N_(n,R) | E_(n,R)] dq/q`.
     - `E_(n,R) = {o <-> X_n in B_R}` under the joint law of walk and percolation.
     - `N_(n,R)` is the number of open edges pivotal for it.
     - See `fpbs-integrated-pivotal-rate-identity`.
   - [F] therefore holds iff this integral is `o(n)` for some `p > p_c`, uniformly in `R >= R_n`.
     Equivalently, the conditional pivotal count has a *sublinear* integrated budget just above `p_c`.
   - A linear budget `<= C n` gives only `lambda(p) <= rho e^(C'(p-p_c))`
     (`fpbs-pivotal-budget-implies-nonuniqueness`), which does not reach [F].
   - On `T_d` the integrated budget from `p_c` to `p` is sublinear exactly for `p <= p_lambda`. So the attack needs an input that
     sees the flat edge. Neither Harris-FKG nor the expansion inputs do; they hold on `H~`, where the
     rate jumps.
   - The complex-analytic version of this attack is not a way around the gap: by
     `fpbs-sublinear-zero-interpolant-iff-flat-rate` it is equivalent to [F].
