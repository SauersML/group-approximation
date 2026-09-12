---
rg: 2
id: deligne-monomial-twisted-modules-no-folner-proof
kind: route
title: Folner coordinates give almost invariant vectors, property (T) gives a finite orbit, and the orbit's line character separates z in a finite quotient
target: deligne-monomial-twisted-modules-have-no-folner-truncations
requires:
  - deligne-triple-cover-finite-residual-is-center
artifacts:
  - research/artifacts/deligne-twisted-group-algebras-2026-09-12.md
---

Artifact Proposition 3.1.
1. Normalized indicators of Folner sets are almost invariant vectors in `l^2(X)`.
2. `Sp_4(Z)` has property (T) (a lattice in higher-rank `Sp_4(R)`), so there is an invariant vector, and its
   level sets give a finite orbit.
3. The stabilizer's preimage `L` has finite index in `E_3` and acts on the line of that basis vector by a
   character `chi` with `chi(z) = w^j != 1`.
4. `L` has (T), as a finite-index subgroup of the finite central extension `E_3` of a Kazhdan group, so its
   abelianization is finite and `ker chi` has finite index.
5. The normal core of `ker chi` is a finite-index normal subgroup missing `z`, against
   `deligne-triple-cover-finite-residual-is-center`.

*Verification by `w4-vf-linear-b` (2026-09-12), Section 22 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS. Re-derived independently: Følner vectors plus (T) give a finite orbit, and the line character on a finite-index (T) subgroup has finite-index kernel missing `z`.*
