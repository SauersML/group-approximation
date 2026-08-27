---
rg: 2
id: commuting-lamp-quotient-structure
kind: claim
title: Structure of the commuting-lamp quotient
distinct_from:
  commuting-lamp-quotient-mf: This is the algebraic identification of the quotient group; the other asks whether that group admits operator-norm microstates.
  corona-hs-radical-is-finite-residual: This is the algebraic identification of the group; the other is a statement about all of its corona representations.
  kun-thom-wreath-weak-mf: That is the open MF question for the Kun--Thom commuting-lamp wreath over a different Kazhdan pair; this is the algebraic identification of the wreath belonging to the affine pair, including its site coordinates, and it decides nothing about MF.
  doubling-quotient-residually-finite: That claim is about lamps indexed by the height line, which is the level-collapse quotient of this group; this claim identifies the group itself, whose lamps are indexed by the full coset space and which is not residually finite.
  literal-telescope-split-normal-form: That claim splits the literal presented group `E` over the same telescope quotient and identifies its lamp kernel as a block amalgam; this one identifies the Clifford witness modulo its sign, where the lamp kernel is elementary abelian and the block structure has collapsed.
artifacts:
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
---

`W/<zeta>` is the permutational wreath product `F_2 wr_{V/Gbar} V`, that is
`F_2[X] semidirect V` with `V` permuting the basis `X = V/Gbar`.  As a
`V`-set,

```text
X = Z x (Z[1/2]/Z)^3,
tau . (n,y) = (n+1, y),
(v,A) . (n,y) = (n, 2^{-n} v + A y)   for (v,A) in T = Z[1/2]^3 sd SL_3(Z),
```

with root `o = (0,0)`, `tau o = (1,0)`, `v_1 tau o = (1, e_1/2)`, and the
level map `X -> Z` equal to the `tau`-exponent.  The `T`-orbits on `X` are
exactly the levels; every `Gbar_k`-orbit is finite.  The surviving defect is
the two-lamp configuration `ubar = e_{(1,0)} + e_{(1,e_1/2)}`.
