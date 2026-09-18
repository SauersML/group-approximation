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
  - research/artifacts/fpbs-zero-free-flat-rate-referee-2026-09-18.md
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

2. **Referee pass and Vitali proof on the n-th roots (2026-09-18, swarm-0917-w8-w8-bs-last1).** Now the route
   `fpbs-zero-free-flat-rate-vitali-proof` (requires `fpbs-critical-walk-correlation`); referee notes in
   `research/artifacts/fpbs-zero-free-flat-rate-referee-2026-09-18.md`. Attempt 1 was checked line by line and
   is correct up to two repairs: its Step 4 used monotonicity of uniqueness without citation (repaired by
   monotonicity of `a_n` in `p`), and its lower bound `lambda>=rho` needs the odd-`n` bound
   `a_(n,R)(p) >= p P(X_(n-1)=o)` on bipartite graphs. The new proof bounds the analytic `n`-th roots
   `h_(n,R)` by `e^M`, applies Montel to the whole family `n>=n_0, R>=n`, and uses Schramm's lemma, Kesten and
   the identity theorem to force every limit to equal `rho`. (a), (b) and (c) follow from the modulus,
   Harris-FKG, and the Cauchy estimate with the finite Russo identity. It also gives the sharper budget
   `o(n)` in (c).

3. **Converse, sharpness and tree calibration (2026-09-18, swarm-0917-w8-w8-bs-last1).** See
   `research/artifacts/fpbs-sublinear-zero-flat-rate-2026-09-18.md`.
   - The theorem extends to analytic interpolants with `o(n)` zeros on a symmetric domain, along a
     subsequence, and dominating `a_n` at one point. In that form it is *equivalent* to the flat rate
     (`fpbs-sublinear-zero-interpolant-iff-flat-rate`).
   - `o(n)` cannot be relaxed to `O(n)`: Chebyshev polynomials are a counterexample.
   - On `T_d` the hypothesis can hold only with `I_+` in `(p_c, (d-1)^(-1/2)]`
     (`fpbs-tree-connection-zeros-linear-past-flat-edge`). On `T_3`, the disc `|z-1/2|<1/4` carries
     linearly many zeros, for example a zero of `a_2000` at `0.7325 + 0.0589 i`, confirmed in exact
     arithmetic. So the tree evidence for (ZG) quoted in the 2026-09-17 artifact must shrink its domain.
   - The theorem itself is unaffected. Its conclusion (a) is now also the open hole
     `fpbs-flat-walk-rate-past-pc-universal`.
