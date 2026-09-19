---
rg: 2
id: corona-hs-radical-proof
kind: route
title: Iterate Kazhdan transport across all telescope levels
target: corona-hs-radical-is-finite-residual
requires:
  - kazhdan-asymptotic-commutant-transport
  - commuting-lamp-quotient-structure
  - commuting-lamp-quotient-finite-residual
artifacts:
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
---

## Direct proof

Transport gives `P = beta(tau) P beta(tau)^*` for the Kazhdan projection `P`
of `Gbar` in the adjoint corona.  Conjugating that identity by
`beta(tau)^{\pm 1}` repeatedly gives `Fix(Gbar_k) = Fix(Gbar)` for every
`k in Z`, in both directions, hence `Fix(Gbar) = Fix(T)` because
`T = union_k Gbar_k`.

The lamp `c_o` commutes with `Gbar = Stab_V(o)`, so its vector is
`Gbar`-fixed and therefore `T`-fixed; translating by `beta(g)` and using
normality of `T` in `V`, the vector of every lamp `c_x` is `T`-fixed.  Since
the `T`-orbits are exactly the levels, every same-level pair
`c_x c_{x'}` has normalized Hilbert--Schmidt distance `0` from `1`.  These
pairs generate `L_0`, and the induced tracial map is a homomorphism.

For the converse, an element outside `L_0` survives in a finite quotient
(`commuting-lamp-quotient-finite-residual`); the left regular permutation
representation of that finite quotient is an honest corona representation, and
a nontrivial translation permutation matrix is at normalized
Hilbert--Schmidt distance `sqrt 2` from the identity.  Section 6 of the cited
note is the complete argument.
