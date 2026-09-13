---
rg: 2
id: congruence-sc-fails-along-levels-with-recurring-divisor
kind: claim
title: Full congruence representations never converge strongly along levels in which a fixed nontrivial modulus recurs
---

ESTABLISHED.  Let `Gamma` be a nonamenable group with finite-index normal
subgroups `Gamma(N)`, `N >= 1`, such that `Gamma(N) <= Gamma(M)` whenever
`M | N` (for example principal congruence subgroups of an arithmetic group).
Put `pi_N = l^2_0(Gamma / Gamma(N))`.  Let `(N_k)` be a sequence of levels and
suppose some `M` with `Gamma(M) != Gamma` divides infinitely many `N_k`.  Then
`(pi_(N_k))` does not converge strongly to `lambda_Gamma`.

In particular the full congruence representations of `SL_1(O_D)` or of
`SL_3(Z)` fail along `N_k = p^k` or `N_k = k!`.  A strongly convergent
congruence sequence must use levels in which each fixed modulus divides only
finitely many terms (for example primes), or keep only the new part at each
level.

Proof: `congruence-sc-fails-along-levels-with-recurring-divisor-proof`.
