---
rg: 2
id: coprime-sector-collapse-is-robust-to-small-p-admixture
kind: claim
title: The coprime-level collapse survives a p-divisible admixture of weight tending to zero
distinct_from:
  odd-congruence-lambda-exact-sector-collapses: that proves the collapse when the Lambda-part is exactly of level coprime to p; this asks for the same conclusion when the Lambda-part is a genuine representation whose p-divisible constituents have weight o(1), which is what the depth-free Atkin--Lehner bound delivers at large primes.
  p-divisible-lambda-exact-mass-vanishes-at-large-primes: that is the theorem producing the o(1) admixture; this is the lemma needed to consume it.
---

**ESTABLISHED (corollary of the coprime theorem; proof in
`coprime-sector-robustness-proof`).**  Let `pi : Gamma = SL_3(Z[1/p]) -> U(M)`
be the restriction of a hyperlinear approximation of
`G_p = <Gamma, t | [t, Lambda] = 1>` (`Lambda = SL_3(Z)`), with microstates
`rho_n` whose `Lambda`-parts are genuine representations
`rho'_n = rho'_(n,0) (+) rho'_(n,p)`, where `rho'_(n,0)` is of level coprime
to `p` and the `p`-divisible part `rho'_(n,p)` has normalized dimension
`delta_n -> 0`.  Then the collapse `(RC3)` holds:
`pi(Lambda)' cap M = pi(Gamma)' cap M`.

**Why it is immediate.**  Replacing `rho'_(n,p)` by the identity changes
each `rho_n(lambda)` by at most `2 delta_n^(1/2)` in normalized
Hilbert--Schmidt norm, so it does not change `pi` at all; the modified
representatives are `Lambda`-exact of coprime congruence type, and
`odd-congruence-lambda-exact-sector-collapses` applies to them verbatim.
The bookkeeping of cross terms that a matrix-level argument would need is
absorbed by the tracial ultraproduct.

**Use.**  With `p-divisible-lambda-exact-mass-vanishes-at-large-primes`
(which delivers `delta_n = O(epsilon_n)` for `p >= 11` regardless of depth)
this closes the entire `Lambda`-exact face of the collapse at primes
`p >= 11`; see `sl3-large-prime-collapse-from-weak-ucp-stability`, whose
only remaining open input is `sl3-z-weakly-ucp-stable`.
