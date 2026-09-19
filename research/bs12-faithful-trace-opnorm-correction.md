---
rg: 2
id: bs12-faithful-trace-opnorm-correction
kind: claim
title: Same-dimension operator-norm correction of BS(1,2) near-representations whose limit trace is faithful
distinct_from:
  bs12-trivially-padded-opnorm-correction: that is the full question (ESS Q3) for all near-representations; this is the sub-question for near-representations whose limit trace is faithful, which by the padding route is equivalent to Q3 modulo regular-padding removal.
---

**OPEN.**

**Statement (Q3_full).**  Let `(A_N, B_N)` in `U(N)`, along a subsequence
`N -> omega`, satisfy `||A_N B_N A_N* - B_N^2|| -> 0`.  Suppose that the
limit trace `g -> lim_omega tr_N w_g(A_N, B_N)` on `BS(1,2)` extends to a
faithful state on `C*(BS(1,2))`.  Then there are exact pairs `(C_N, Z_N)`
in `U(N)` with `||A_N - C_N|| + ||B_N - Z_N|| -> 0` along `omega`.

The limit is a well-defined character, by
`bs1n-hs-stable-levit-vigdorovich` applied to the normal-form extension of
the pair.

**Relation to the census.**  By `bs12-matrix-lift-pairs-have-zero-kl-class`
item 4, every twisted-clock pair `(D_N, W exp(isH))` has limit trace
`tau_reg`, which is faithful.  So the wave-14 question "is liminf d(s,N) > 0
for some s" is exactly a test of Q3_full at the regular trace.  A positive
answer refutes Q3_full, and hence refutes Q3 and TPC.

**Status.**
- Q3_full follows from HS-stability together with
  `bs12-full-lift-uniqueness-in-matrix-ultraproducts`; this is the route
  `bs12-faithful-trace-opnorm-correction-via-uniqueness`.
- TPC follows from Q3_full together with `bs12-regular-padding-is-removable`;
  this is the route
  `bs12-trivially-padded-opnorm-correction-via-faithful-padding`.

## Attempts

- 2026-09-19 (swarm-0917-w15-w15-ptm-follow): isolated as the core of Q3.
  All K-theoretic obstructions vanish here.  What remains is
  de-amplification and absorption.
