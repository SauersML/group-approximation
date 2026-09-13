---
rg: 2
id: sl4z-block-sl2-norm-four-unless-unipotent-spectrum-is-full-proof
kind: route
title: Factor through a finite congruence quotient and apply Magee-de la Salle on one nonzero isotypic summand
target: sl4z-block-sl2-norm-four-unless-unipotent-spectrum-is-full
requires: [sln-z-unipotent-spectrum-finite-or-full-torus, sl4z-representations-have-sl2-invariant-vectors]
artifacts:
  - research/artifacts/sl4z-mf-corona-reduction-2026-09-13-part2.md
---

Artifact part 2, Section 2.

1. **A finite quotient.**  The spectrum is not `T^3`, so by
   `sln-z-unipotent-spectrum-finite-or-full-torus` `sigma` factors through
   `C*(G)`, `G = SL_4(Z/NZ)`.  This algebra is `sum_rho M_(d_rho)`, with central
   projections `p_rho`.
2. **One summand survives.**  `sigma` is unital, so `sigma(p_rho) != 0` for some
   irreducible `rho`.  A nonzero *-homomorphism on the simple summand `C*(G) p_rho` is
   isometric.
3. **Norm four there.**  Pull `rho` back to `SL_4(Z)`; it is finite-dimensional, so by
   `sl4z-representations-have-sl2-invariant-vectors` it has a nonzero block-`SL_2(Z)`
   fixed vector.  Hence `||rho(S + S^-1 + T + T^-1)|| = 4`.
4. **Conclude.**
   `||sigma(z)|| >= ||sigma(z) sigma(p_rho)|| = ||z p_rho||_(C*(G)) = ||rho(z)|| = 4`,
   and `||sigma(z)|| <= 4` always.  On `H`, `sigma(p_rho) H != 0` is `rho`-isotypic, so
   it contains `rho`'s fixed vectors.
