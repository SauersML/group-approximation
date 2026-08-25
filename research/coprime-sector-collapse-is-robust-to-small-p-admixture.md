---
rg: 2
id: coprime-sector-collapse-is-robust-to-small-p-admixture
kind: claim
title: The coprime-level collapse survives a p-divisible admixture of weight tending to zero
distinct_from:
  odd-congruence-lambda-exact-sector-collapses: that proves the collapse when the Lambda-part is exactly of level coprime to p; this asks for the same conclusion when the Lambda-part is a genuine representation whose p-divisible constituents have weight o(1), which is what the depth-free Atkin--Lehner bound delivers at large primes.
  p-divisible-lambda-exact-mass-vanishes-at-large-primes: that is the theorem producing the o(1) admixture; this is the lemma needed to consume it.
---

**OPEN (technical).**  Let `pi : Gamma = SL_3(Z[1/p]) -> U(M)` be the
restriction of a hyperlinear approximation of `G_p = <Gamma, t | [t, Lambda] = 1>`
(`Lambda = SL_3(Z)`), with microstates `rho_n` whose `Lambda`-parts are genuine
representations `rho'_n = rho'_(n,0) (+) rho'_(n,p)`, where `rho'_(n,0)` is of
level coprime to `p` and the `p`-divisible part `rho'_(n,p)` has normalized
dimension `delta_n -> 0`.  Then the collapse `(RC3)` holds:
`pi(Lambda)' cap M = pi(Gamma)' cap M`.

**Expected proof.**  Compress to the range `V_n` of `rho'_(n,0)`: the
projection `P_n` onto it lies in `rho'_n(Lambda)'`, so a unitary
`k in pi(Lambda)' cap M` has lifts `k_n` with `||k_n - P_n k_n P_n - (1-P_n) k_n (1-P_n)||_2 <= 2 sqrt(delta_n)`
and `||(1 - P_n) k_n||_2^2 <= delta_n`.  The compressed corrector
`P_n rho_n(h) P_n` is within `O(sqrt(delta_n))` of a unitary on `V_n`
(both `rho_n(h)` and `P_n` are almost respected by the relators), and on
`V_n` the exact slot `rho'_(n,0)(h-bar)` exists.  The Weyl-relation
evaluation of `odd-congruence-lambda-exact-sector-collapses` then runs with
errors `O(sqrt(delta_n)) + o(1)` and forces the compressed corrector to `1`,
whence `k_n` commutes with `rho_n(h)` up to `o(1)`.  The only new content is
bookkeeping of the `O(sqrt(delta_n))` cross terms through that evaluation,
which uses finitely many relators.

## Attempts

- Deferred pending a line-by-line pass through the Weyl-relation argument
  with the compressed corrector; no obstruction is visible, since every step
  of that argument is an identity in finitely many matrices perturbed by
  `O(sqrt(delta_n))`.
