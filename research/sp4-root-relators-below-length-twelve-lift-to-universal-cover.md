---
rg: 2
id: sp4-root-relators-below-length-twelve-lift-to-universal-cover
kind: claim
title: Every relation of Sp4(Z) of length below twelve in the eight root generators holds in the universal-cover lattice
artifacts:
  - research/artifacts/maslov-mod3-sector-numerics-2026-09-05.md
  - experiments/maslov_sector/presentation.py
  - experiments/maslov_sector/lifted_relators.txt
distinct_from:
  sp4-fd-projective-multiplier-is-finite: that bounds the finite-dimensionally realizable projective multipliers of Sp_4(Z); this is an exact statement about which relators of a fixed generating set carry the universal-cover class, with no representation theory involved.
  deligne-triple-cover-fd-central-invisibility: that is Deligne's theorem that the central mark dies in every finite-dimensional representation; this locates the mark inside the relation module of a specific presentation window, which is what any relator-energy formulation of the Maslov sector needs.
---

Let `S` be the eight root elements `x_alpha(1)` of `Sp_4(Z)` (roots of
`C_2`, with `x_alpha(t) = I + t N_alpha`), and let
`Sp~_4(Z)` be the pullback of `Sp_4(Z)` to the universal cover of
`Sp_4(R)`, a central extension by `Z = <zeta>`.  Lift each generator along
its one-parameter subgroup.  Then:

1. every word in `S` of length at most `11` that is trivial in `Sp_4(Z)` is
   trivial in `Sp~_4(Z)`;
2. among the `270,118` cyclically reduced relators of length `12` (up to
   rotation and inversion), exactly `20` lift to `zeta`, and all others lift
   to `1`; the twenty are the length-12 relators of the two long-root copies
   of `SL_2(Z) = <x_{2e_i}(1), x_{-2e_i}(1)>` whose lift to the braid group
   `B_3` is the kernel generator `Delta^4`;
3. the exponent-sum lattice of all `304,412` relators of length at most `13`,
   with the lift column appended, has central relation generator `1`, so
   `zeta` lies in the commutator subgroup of the group these relators
   present.

**ESTABLISHED (computational).**  The lift exponent of a relator is the
winding number of `det` of the `U(2)`-part of the concatenated one-parameter
path, an integer computed to `2e-15` for every relator; see the artifact and
`experiments/maslov_sector/presentation.py`.  Clause 1 is exhaustive: the
radius-5 ball contains every closed loop of length at most `11`, and the
fundamental cycles of the breadth-first tree generate them.

## Use

Any relator-energy formulation of the mod-three Maslov sector
(`maslov-mod3-projective-defect-gap`) must use a presentation window of
length at least twelve, and the entire sector phase is carried by the long-root
`w^4` relators; the short-root `w^4` relators and all Steinberg commutator
relations are sector-blind.
