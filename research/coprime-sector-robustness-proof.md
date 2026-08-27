---
rg: 2
id: coprime-sector-robustness-proof
kind: route
title: A summand of vanishing weight is invisible in the tracial ultraproduct, so the coprime theorem applies to a modified representative sequence
target: coprime-sector-collapse-is-robust-to-small-p-admixture
requires:
  - odd-congruence-lambda-exact-sector-collapses
---

Let `(rho_n)` be the microstates, `M = prod_U M_(d_n)`, `pi = [rho_n]` on
`Gamma`, and `rho_n|_Lambda = rho'_(n,0) (+) rho'_(n,p)` as in the claim, with
`P_n` the projection onto the range of `rho'_(n,0)` and `tau(1 - P_n) = delta_n -> 0`.

Define a new sequence on `Lambda` by `rho''_n(lambda) := rho'_(n,0)(lambda) (+) 1`
(the identity on the range of `1 - P_n`) and keep `rho''_n(h) := rho_n(h)`;
extend to words in `Lambda` and `h` in the obvious way.  Each `rho''_n|_Lambda`
is a genuine representation of `Lambda` factoring through `SL_3(Z/m'_n)` with
`m'_n` coprime to `p`.  For every `lambda in Lambda`,

```text
|| rho''_n(lambda) - rho_n(lambda) ||_2  =  || (1 - P_n)(rho'_(n,p)(lambda) - 1)(1 - P_n) ||_2
                                         <=  2 tau(1 - P_n)^(1/2)  =  2 delta_n^(1/2)  ->  0,
```

so `[rho''_n(lambda)] = [rho_n(lambda)] = pi(lambda)` in `M`.  Hence `(rho''_n)`
is another representative sequence of the same `pi`, and its
`Lambda`-restrictions are genuine representations of level coprime to `p`:
`pi` is `Lambda`-exact of coprime congruence type in the sense of
`odd-congruence-lambda-exact-sector-collapses`.  Its proof
(`odd-congruence-lambda-exact-sector-collapse-proof`) uses only such a
representative sequence -- the property (T) lifting into the congruence
commutant tower `R_U = prod_U rho''_n(Lambda)'`, the exact slot
`V' = [rho''_n(lambda_(h,n))]`, and the Weyl relations, all evaluated in
`M` -- so it yields `pi(Lambda)' cap M = pi(Gamma)' cap M` verbatim.  No
bookkeeping of cross terms is needed: the tracial ultraproduct performs it.
