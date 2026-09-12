---
rg: 2
id: sl3-double-swap-outlier-confinement-proof
kind: route
title: The fold mark evaluates the sector theorems against the swap involution on the exact face
target: sl3-double-swap-involution-is-outlier-carried
requires:
  - arithmetic-double-swap-extension-is-binary-coset-wreath
  - odd-congruence-lambda-exact-sector-collapses
  - p-divisible-lambda-exact-mass-vanishes-at-large-primes
  - coprime-sector-collapse-is-robust-to-small-p-admixture
---

Let `phi_n : E_p -> U(d_n)` be a hyperlinear approximation with the
canonical character, `M = prod_U M_(d_n)` the tracial ultraproduct it
defines, `pi : Gamma -> U(M)` the restriction and `s = [phi(s)] in U(M)`.
In `M` the relations hold exactly: `s^2 = 1`, `s in pi(Lambda)' cap M`,
and `tau(pi(gamma) s^r)` is the canonical character of `E_p`, so
`tau(s) = 0` and `tau(pi(w)) = 0` for the fold mark `w = h s h^(-1) s`
(`w` is a reduced amalgam word, per
`arithmetic-double-swap-extension-is-binary-coset-wreath`).

The distance of `phi_n|_Lambda` to the set of genuine unitary
representations of `Lambda` (normalized HS on a fixed generating set,
flexible padding allowed) has a limit `delta` along the ultrafilter.
Suppose `delta = 0`; we derive a contradiction, which proves the theorem.

If `delta = 0` the microstates may be corrected on a vanishing-weight
corner so that their `Lambda`-parts are genuine finite-dimensional
representations `rho'_n`; by superrigidity and the congruence subgroup
property these factor through `SL_3(Z/(p^(D_n) m'_n))`, `p` not dividing
`m'_n`.  The `h`-twist defect `epsilon_n` on the generators of
`Lambda cap h^(-1) Lambda h` tends to zero because `phi_n` is
asymptotically multiplicative on `Gamma`.
`p-divisible-lambda-exact-mass-vanishes-at-large-primes` then gives
`a_p (1 - nu_(0,n)) <= epsilon_n^2 / kappa_0^2` with
`a_p = min(4 c_p - 3, 1/3) > 0` at `p >= 11`, so the `p`-divisible
weight tends to zero, independently of the depths `D_n`.
`coprime-sector-collapse-is-robust-to-small-p-admixture` absorbs the
vanishing admixture, and `odd-congruence-lambda-exact-sector-collapses`
applies to the resulting coprime-level `Lambda`-exact microstates of
`pi`, yielding the commutant identity on this sector:

```text
pi(Lambda)' cap M = pi(Gamma)' cap M.                     (OS1)
```

The swap involution `s` lies in the left side, hence commutes with
`pi(h)`.  Then

```text
tau(pi(w)) = tau(u_h s u_h^* s) = tau(u_h u_h^* s^2) = tau(1) = 1,
```

against the canonical value `0` -- contradiction.  So `delta > 0`: the
lattice restrictions are uniform outliers.  (The correction step and the
sector bookkeeping are exactly those of
`sl3-large-prime-collapse-from-weak-ucp-stability`, with one difference:
there, stability SUPPLIED the `delta = 0` case for every microstate and
the argument closed the collapse; here nothing supplies it, and the same
machinery instead proves that `delta = 0` is impossible in the presence
of the involution, unconditionally.)
