---
rg: 2
id: titz-witzel-lp-failure-proof
kind: route
title: Brown identification, apartment retraction, and Ioana-Spaas-Wiersma Corollary D
target: titz-witzel-lattices-fail-lp
requires:
  - titz-witzel-simple-kazhdan-cat0-lattices-exist
---

Three steps, each with its source.

1. `H^2(Gamma, Z Gamma) = H^2_c(X)` by `(TW1)` of the citation route
   (free cocompact action on the contractible building `X`).

2. `H^2_c(X) != 0`.  Fix an apartment `A subset X`, a flat Euclidean
   plane, and a chamber `c subset A`.  The building retraction
   `rho_(A,c) : X -> A` restricts to the identity on `A` and does not
   increase (gallery) distance to `c`, so preimages of bounded sets are
   bounded: `rho` is a proper retraction and `i : A -> X` is a proper
   inclusion with `rho o i = id`.  Functoriality of compactly supported
   cohomology under proper maps makes `H^2_c(A) = H^2_c(R^2) = Z` a
   retract of `H^2_c(X)`, which is therefore nonzero.  (The same
   three-line argument is recorded with its DDJMO context in
   research/artifacts/isw-ddjmo-cr-cohomology-sources-2026-08-21.md,
   where the general computation of `H^*_c` of building realizations is
   source-verified as Davis--Dymara--Januszkiewicz--Meier--Okun,
   arXiv:0806.2412.)

3. Ioana--Spaas--Wiersma, arXiv:2006.01874, Corollary D (verbatim in the
   same artifact): for a countable group with property (T) and
   `H^2(Gamma, Z Gamma) != 0`, the full C*-algebra `C^*(Gamma)` does not
   have the LP.  Property (T) holds by Theorem A of the citation; both
   hypotheses pass to the finite-index simple subgroups.
