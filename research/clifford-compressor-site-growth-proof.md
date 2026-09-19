---
rg: 2
id: clifford-compressor-site-growth-proof
kind: route
title: Monoid divisibility, infinite site orbits, and a Pimsner--Popa test projection
target: clifford-compressor-site-growth
requires: []
artifacts:
  - notes/TRUE_CLIFFORD_COMPRESSOR_SITE_GROWTH.md
---

Complete written argument in the artifact.  Four steps.

1. `X^Gamma={g Gamma : g^(-1) in P_Gamma}` and
   `P_Gamma intersect L=L_+` (established in
   `FALSE_COMPRESSION_SEMIGROUP_ORE_NO_GO.md`) give an injection
   `L_+ -> X^Gamma`, `p |-> p^(-1)Gamma`, with
   `s.(p^(-1)Gamma) in X^Gamma` iff `p in L_+ s`.
2. If `L_+ minus L_+ s` were finite, then `(I+n e_(ij))s^(-1)` would be
   nonnegative for infinitely many `n`, forcing every row of `s^(-1)` to be
   nonnegative; a nonnegative integer matrix with nonnegative inverse is a
   permutation matrix, which normalizes `Gamma`.
3. For `ell=s p^(-1)` with `ell^(-1)` not nonnegative, the monomials
   `m E_(bc)` witness that `Lambda_+ minus ell Lambda_+` is infinite, and the
   `(1,2)` entries of `x_(12)(x^mu)` separate cosets, so
   `[Gamma:Gamma intersect ell Gamma ell^(-1)]=infinity`: every new site has
   infinite `Gamma`-orbit.
4. The Kazhdan average realizes `E_N`; a Clifford monomial over a finite set
   with infinite orbit has vanishing average, by orthogonality of distinct
   monomials and vanishing of the Kazhdan projection in a quasi-regular
   representation of infinite index.  Hence
   `q=product (1+i c c')/2` over `k` disjoint pairs of new sites lies in
   `N_s`, has trace `2^(-k)` and `E_N(q)=2^(-k)1`, so the Pimsner--Popa
   constant is at most `2^(-k)` for every `k`.
