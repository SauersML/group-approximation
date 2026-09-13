---
rg: 2
id: sl3z-prime-level-sc-needs-cubic-chebotarev-primes
kind: claim
title: A strongly convergent prime-level sequence for SL_3(Z) must run over cubic-twist cuspidal constituents at primes where all small integers are cubes
artifacts:
  - research/artifacts/sl3z-prime-level-witness-completeness-2026-09-13.md
---

ESTABLISHED (unreviewed).  Let `rho_i` be nontrivial irreducible
representations of `SL_3(F_(p_i))`, pulled back to `SL_3(Z)`, with
`p_i -> infinity` and `rho_i -> lambda_(SL_3(Z))` strongly.  Then for every `M`,
for all large `i`:

- (a) `p_i == 1 mod 3`;
- (b) `rho_i` is a constituent of the restriction of a cubic-twist-invariant
  cuspidal representation of `GL_3(F_(p_i))`;
- (c) every integer `1 <= m <= M` is a cube mod `p_i`.

So `p_i` eventually splits completely in `Q(zeta_3, 2^(1/3), ..., M^(1/3))` for
every `M`.  The witnesses are the block `SL_2(Z)` and the integral principal
subgroups `H_m = diag(m,1,1) Sym^2(SL_2(Z)) diag(m,1,1)^(-1) cap SL_3(Z)`.  For
`p` not dividing `2m`, `H_m` reduces onto `Omega^(m mod p)`.  If a small integer
`m` is a non-cube mod `p_i`, then `1`, `m`, `m^2` represent all three cube
classes.  By `sl3z-prime-level-invariant-witnesses-are-complete` some `H_m`
then has fixed vectors, and a fixed matrix-valued Kesten element sees norm 1.

What it leaves open.  This is a necessary condition, not a refutation.  Along
such primes the principal fixed vectors of `rho_i` sit at witnesses `H_m` with
`m` at least the least non-cube mod `p_i`, and those witnesses move to
infinity.  A refutation of `sl3z-purely-matricial-field` at prime levels would
need a norm excess that survives this migration.  Mixed levels escape all these
witnesses in any case (`sl3z-has-no-invariant-vector-witnesses`).

Proof: `sl3z-prime-level-sc-needs-cubic-chebotarev-primes-proof`.
