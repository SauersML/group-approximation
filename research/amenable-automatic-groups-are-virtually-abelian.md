---
rg: 2
id: amenable-automatic-groups-are-virtually-abelian
kind: claim
title: Every amenable automatic group is virtually abelian
distinct_from:
  automatic-groups-have-contractible-rips-complexes: that asks for a contractible Rips complex for every automatic group; this asks that amenability force an automatic group to be virtually abelian, an algebraic rigidity statement with no complex in it
  torsion-free-automatic-groups-have-finite-cd: that bounds the cohomological dimension of torsion-free automatic groups; this forces amenable automatic groups to be virtually abelian, which would bound it only in the amenable case
---

**OPEN.** If `G` is amenable and automatic (Epstein et al., *Word Processing in
Groups*, 1992), then `G` has an abelian subgroup of finite index.

It matters here because it would decide one half of the interaction between
Zaremsky Problems 2.1 and 2.2: together with `thompson-f-is-amenable` it gives
`thompson-f-is-not-automatic` (route
`thompson-f-not-automatic-via-amenable-rigidity`).

## Attempts

- **Nilpotent groups.** The nilpotent case is classical: nilpotent automatic
  groups are virtually abelian (Epstein et al.). Hauze's dissertation
  (arXiv:1801.01965, Chapter 1) lists nilpotent groups among the standard
  non-automatic examples. The general amenable case does not follow.
- **Metabelian test cases.** `BS(1, n)` for `n >= 2` is not automatic
  (Hauze's list again names Baumslag–Solitar groups). `Z ≀ Z` and the
  lamplighter groups are not finitely presented, so they are not automatic.
  Neither is a counterexample, and no argument for general solvable groups is
  recorded.
- **Where a proof would need input.** Automaticity gives a quadratic
  isoperimetric inequality, type `F_∞` and a regular normal form language.
  Amenability gives Følner sets. No known mechanism turns Følner sets plus the
  synchronous fellow traveller property into a finite-index abelian subgroup.
  Not attempted beyond this survey. The literature check this session was
  bounded (direct arXiv fetches only) and found no statement of this claim,
  proved or refuted.
