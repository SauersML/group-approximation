---
rg: 2
id: sl3z-prime-level-sc-needs-cubic-chebotarev-primes-proof
kind: route
title: A matrix Kesten element over the block and H_1..H_(M^2) forces cuspidality, splitting, and a missing cube class that the powers of a non-cube would fill
target: sl3z-prime-level-sc-needs-cubic-chebotarev-primes
requires: [sl3z-prime-level-invariant-witnesses-are-complete]
artifacts:
  - research/artifacts/sl3z-prime-level-witness-completeness-2026-09-13.md
---

Artifact, sections "Integral witnesses" and "Corollary F".

1. `H_m` contains `diag(m,1,1) Sym^2(Gamma(m)) diag(m,1,1)^(-1)`, so it is
   nonamenable and finitely generated.  For `p` not dividing `2m` its reduction
   is `Omega^(m mod p)`: `Gamma(m)` is onto `SL_2(F_p)`, and elements of `H_m` come
   from `p`-integral `g`.
2. Put `y_M = diag(L_(B_2(Z))/4, L_(H_m)/|S_m| : m <= M^2)`.  Then
   `||lambda(y_M)|| < 1` by Kesten, while `||rho(y_M)|| = 1` as soon as `rho` has a
   fixed vector for one of these subgroups.  Strong convergence with matrix
   coefficients therefore removes all such fixed vectors for large `i`.
3. Part 1 of `sl3z-prime-level-invariant-witnesses-are-complete` makes
   `rho_i` cuspidal.  Part 2 with `H_1` forces a split restriction, so
   `p_i == 1 mod 3`.  Part 3 says the set `E_i` of missed cube classes is not
   everything.  But `E_i` contains the classes of all `m <= M^2`.  If some
   `m <= M` were a non-cube, the classes of `1`, `m`, `m^2` would already be
   everything.
