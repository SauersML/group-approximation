---
rg: 2
id: literal-mark-quotient-corona-blindness-proof
kind: route
title: Transport across levels in the literal quotient
target: literal-mark-quotient-corona-blindness
requires: [kazhdan-asymptotic-commutant-transport, literal-mark-quotient-finite-residual]
artifacts:
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
---

## Direct proof

The transport identity `P = beta(tau) P beta(tau)^*` conjugated by
`beta(tau)^{\pm 1}` gives `Fix(Gbar_k) = Fix(Gbar)` for every `k in Z`,
hence `Fix(Gbar) = Fix(T)` since `T` is the union of the levels.  The lamp
`c_o` commutes with `Gbar = Stab_V(o)`, so its Hilbert--Schmidt vector is
`T`-fixed; translating by `beta(g)` and using normality of `T` in `V` makes
every lamp vector `T`-fixed.  The `T`-orbits are the levels, so every
same-level lamp pair lies in the kernel of the induced tracial
representation, which is normal and therefore contains `R`.

Conversely, an element outside `R` survives in a finite quotient by
`literal-mark-quotient-finite-residual`, and the left regular permutation
representation of that finite quotient is a corona representation in which a
nontrivial element sits at normalized Hilbert--Schmidt distance `sqrt 2` from
the identity.  Section 9 of the cited note is the complete argument.
