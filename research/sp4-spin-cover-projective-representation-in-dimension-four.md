---
rg: 2
id: sp4-spin-cover-projective-representation-in-dimension-four
kind: claim
title: Sp4(Z) has an explicit four-dimensional projective unitary representation whose Z/2 class is nonzero and not metaplectic
artifacts:
  - research/artifacts/maslov-mod3-sector-numerics-2026-09-05.md
  - experiments/maslov_sector/spin_seed.py
  - experiments/maslov_sector/spin_phases.py
  - experiments/maslov_sector/seed_spin_d4.json
distinct_from:
  sp4-fd-projective-multiplier-is-finite: that proves the subgroup of finite-dimensionally realizable multipliers is finite; this exhibits one nontrivial realizable multiplier concretely, in dimension four, with its generator matrices.
  sp4-root-relators-below-length-twelve-lift-to-universal-cover: that computes the universal-cover lifts of the root relators; this uses those lifts only to show that the class realized here is not the reduction of the universal-cover class.
---

The eight root generators `x_alpha(1)` of `Sp_4(Z)` act on the six odd theta
characteristics of genus two through the affine action
`(m', m'') -> (D m' - C m'' + diag(CD^T), -B m' + A m'' + diag(AB^T))` mod `2`,
identifying `Sp_4(Z) -> Sp_4(F_2) = S_6`.  Pulling back the basic spin
representation of the double cover of `S_6` (Clifford algebra of the
five-dimensional standard representation) gives eight explicit unitaries
`rho(s) in U(4)` such that

1. `rho(r) = +-I` for every relator `r` among the `304,412` cyclically
   reduced relators of length at most `13` in these generators (so `rho` is a
   projective representation of `Sp_4(Z)` with multiplier in `{+-1}`);
2. no rescaling of the eight generators by signs makes every `rho(r) = +I`
   (the class in `H^2(Sp_4(Z); Z/2)` is nonzero);
3. no rescaling makes `rho(r) = (-1)^{k_r} I` with `k_r` the universal-cover
   lift exponents (the class is not the metaplectic reduction of the
   universal-cover class).

**ESTABLISHED (computational).**  Clauses 2 and 3 are linear systems over
`F_2` in the eight signs, with one equation per relator, found inconsistent
by elimination; clause 1 is a direct check on all relators.  A sign
rescaling changes `rho(r)` by the exponent-sum character, which is the only
freedom a coboundary has on a fixed generating set, so inconsistency of the
sign system proves the class statements.  The matrices are in the seed file.
