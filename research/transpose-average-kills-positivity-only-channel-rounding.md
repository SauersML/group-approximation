---
rg: 2
id: transpose-average-kills-positivity-only-channel-rounding
kind: claim
title: The transpose average is an exact positive trace-preserving idempotent at dimension-free distance from every matrix expectation, so channel rounding must use two-positivity at the product step
distinct_from:
  bistochastic-near-idempotents-round-dimension-free: that is the open rounding premise for completely positive maps; this proves the premise is false once complete positivity is weakened to positivity, and locates the only step where the missing hypothesis can enter.
  mub-sum-idempotents-have-uniform-cp-distance: that shows one non-CP sum-of-masas idempotent is uniformly far from UCP maps, so it cannot be a counterexample shape; this uses a positive non-CP idempotent as a certificate that a whole class of proof arguments proves a false statement.
  bistochastic-channel-rounding-fails: that asks for completely positive counterexamples; the map here is not completely positive and is uniformly far from all CP maps, so it is not a counterexample to the premise.
artifacts:
  - research/transpose-average-kills-positivity-only-channel-rounding-proof.md
  - experiments/channel-rounding-2026-09-17/transpose_obstruction.py
  - experiments/channel-rounding-2026-09-17/transpose_obstruction_output.txt
---

**ESTABLISHED.**

Normalized trace `tau=Tr/d`, `||y||_2=tau(y*y)^(1/2)`, and
`||T||_(infinity->2)=sup_(||x||_op<=1)||T(x)||_2`. Let `theta` be the
transpose on `M_d`, `d>=2`, and put

```text
S_d = (id + theta)/2 .
```

**Theorem.**

1. `S_d` is unital, positive, trace-preserving, self-adjoint on
   `L^2(M_d,tau)`, satisfies Kadison's inequality `S(h^2)>=S(h)^2` for
   Hermitian `h`, and is exactly idempotent. It is not 2-positive, and the
   Schwarz inequality fails at `e_12`.
2. For every unital `*`-subalgebra `A` of `M_d`,
   `||S_d-E_A||_(infinity->2) >= sqrt((d-1)/(2d)) >= 1/2`.
   Equality holds in the Haar lower bound for `A=M_d` and for the diagonal masa.
3. For every completely positive `T:M_d->M_d`, with no unitality or trace
   condition, `||S_d-T||_(infinity->2) >= sqrt((d-1)/(8d)) >= 1/4`.
4. The range of `S_d` is the real-symmetric matrices. For real symmetric `a,b`,
   `S_d(ab)-ab=-[a,b]/2`. With `a=Z(x)I`, `b=X(x)I` (`d` even),
   `||S_d(ab)-ab||_2=1` even though the idempotence defect is `0`.
5. Exact two-positive dichotomy. If `P:M_d->M_d` is unital, 2-positive,
   trace-preserving, `L^2`-self-adjoint and exactly idempotent, then
   `P=E_A` for the `*`-subalgebra `A=P(M_d)`.

**Corollary: a class-killing obstruction.** Let `f` be any function with
`f(0)<1/2`. The implication "`P` is unital, positive, trace-preserving,
`L^2`-self-adjoint, Kadison, with `||P^2-P||_(infinity->2)<=delta`, implies
`||P-E_A||_(infinity->2)<=f(delta)` for some `A`" is false in every
dimension. It already fails at `delta=0`, and the gap stays above `1/2` for
all `d`. It stays false under perturbation: a map within `r` of `S_d` is at
distance at least `1/2-r` from every expectation.

So an argument for `bistochastic-near-idempotents-round-dimension-free`
proves a false statement if it only uses:

- the order structure: positivity, Kadison inequalities, pinched-flow
  weights `tau(e_l P(e_j))`, spectral cutoffs, coarea or Cheeger peeling of
  `P(e)` for projections `e`;
- unitality, trace preservation, `L^2` self-adjointness;
- mixed-norm near-idempotence.

By item 5 the missing input is exactly two-positivity (Schwarz).

The failing step is fixed: passing from the range to an associative
algebra, meaning uniform product closure of `P((M_d)_1)`. That is estimate
(4.4) of Section 4 of
`research/artifacts/leavitt-kazhdan-heat-rounding-boundary-and-factorial-center-countermodel-2026-09-08.md`,
which uses Stinespring. Item 4 shows the estimate is false for positive maps
with `epsilon=0`. Positivity alone closes the range only under the Jordan
product `(ab+ba)/2`, as in Effros--Stormer. It cannot produce the associative
algebra the premise asks for.

**Calibration.** For commutative symmetric Markov operators, positivity
equals complete positivity. Rounding there holds
(`symmetric-markov-near-idempotents-round-to-partitions`), and `S_d` has no
commutative analogue. On exact expectations `E_A` every bound above is
consistent: `S_d` attains the Haar bound against `A=M_d`.

**What remains.** The premise with CP weakened to 2-positivity is not
settled by this. It is the sharpest positivity-type version still possibly
true, and any proof must push the Schwarz defect through arbitrarily long
products (item 5 is its exact case).

The classical ingredients are the transpose as a positive non-CP map,
Kadison's inequality, Effros--Stormer on ranges of positive projections, and
Choi--Effros. The quantitative mixed-norm gaps, the Haar--Choi identity used
for them, and the audit against the rounding premise are what this claim
adds. Numerical verification for `d=2..6`:
`experiments/channel-rounding-2026-09-17/transpose_obstruction.py`.
