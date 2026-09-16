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
- 2026-09-13 (lane z4-01-amen-auto-rips): **consequences for Problem 4.1.** Every
  finitely generated virtually abelian group has a contractible Rips complex
  (`virtually-abelian-groups-have-contractible-rips-complexes`, established). So this
  claim gives a yes answer to Zaremsky Problem 4.1 (route
  `amenable-automatic-rips-via-virtually-abelian`). On its own it also gives
  `thompson-f-is-not-both-amenable-and-automatic` (route
  `thompson-f-not-both-via-amenable-automatic-virtually-abelian`). The Dehn
  function cannot supply the proof: the higher Heisenberg groups `H_(2k+1)`,
  `k >= 2`, are nilpotent, not virtually abelian, and have quadratic Dehn function
  (Allcock; Olshanskii–Sapir; from memory), and so does `F` (Guba).
- 2026-09-16 (lane swarm-amenable-automatic-groups-are-): **status, a dichotomy and a
  split into two open halves.** Details are in
  `research/artifacts/amenable-automatic-groups-are-virtually-abelian-2026-09-16.md`.
  - *Status.* Rees's survey (arXiv:2205.14911v1, pp. 14 and 27, read 2026-09-16) calls
    even the soluble case open (Thurston's conjecture). The best result is Romankov's
    theorem that soluble biautomatic groups are virtually abelian (arXiv:1511.00223v1).
    arXiv API searches on 2026-09-16 found no 2024–2026 progress.
  - *Growth dichotomy (proved).* Every automatic group is virtually abelian or contains a
    free subsemigroup of rank 2 (`automatic-groups-virtually-abelian-or-free-subsemigroup`,
    route `automatic-va-or-free-subsemigroup-proof`). So a counterexample has exponential
    growth. This does not reach the target, because every non-virtually-nilpotent soluble
    group already has exponential growth.
  - *Equivalence (proved from imports).* The target holds if and only if both
    `soluble-automatic-groups-are-virtually-abelian` (S) and
    `amenable-automatic-groups-are-elementary-amenable` (EA) hold. The direction to the
    target is route `amenable-automatic-va-via-ea-and-soluble-case`, which uses type
    `F_∞`, Kropholler–Martínez-Pérez–Nucinkis and finite-index inheritance. The converses
    are `soluble-automatic-va-from-amenable-case` and
    `amenable-automatic-ea-from-virtually-abelian-case`. (EA) also follows from
    `every-f-infinity-amenable-group-is-elementary-amenable` (route
    `amenable-automatic-ea-via-f-infinity-amenable-ea`).
  - *Soluble half.* Given Harkins' theorem
    (`polycyclic-automatic-groups-are-virtually-abelian`), (S) is equivalent to
    `soluble-automatic-groups-are-polycyclic`. Romankov's biautomatic proof survives for
    automatic groups up to "torsion-free, finite cohomological dimension, soluble minimax,
    nilpotent-by-(virtually abelian)". It fails at the Gersten–Short `UT_3(Z)` exclusion
    and at the minimal condition on centralizers, both of which are biautomatic-only
    tools.
  - *Dead ends.* A quadratic Dehn function alone does not exclude non-polycyclic
    metabelian groups (de Cornulier–Tessera, arXiv:1003.0148, abstract only). Growth
    gives nothing beyond the dichotomy.
