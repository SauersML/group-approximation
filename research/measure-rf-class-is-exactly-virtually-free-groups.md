---
rg: 2
id: measure-rf-class-is-exactly-virtually-free-groups
kind: claim
title: A finitely generated group has all its full-support invariant-measure Cantor actions residually finite iff it is virtually free
artifacts:
  - research/artifacts/un-rf-beyond-free-2026-09-13-part2.md
---

**OPEN.** Let `𝔑` be the class of countable groups all of whose continuous Cantor actions with a full-support
invariant probability measure are residually finite (Kerr–Nowak). Conjecture: a finitely generated group lies in
`𝔑` iff it is virtually free.

A minimal-free variant is also open: for `Γ` not virtually free, is there a *minimal topologically free* Cantor
action with an invariant measure that is not residually finite?

## Attempts

- **Proved inclusions.**
  - Virtually free ⊆ `𝔑` (`virtually-free-group-measure-actions-are-rf`).
  - No group containing `Z^2` is in `𝔑` (`z2-containing-groups-have-non-rf-measure-actions`).
  - `𝔑` is closed under subgroups and finite-index overgroups (`measure-rf-property-passes-to-subgroups`).
- **Obstruction mechanism.** Any closed invariant subset of an SFT with no finite orbit that carries a
  full-support invariant measure is non-RF (`sfts-without-finite-orbits-are-not-residually-finite-actions`).
  - For amenable groups every such SFT has a minimal subset with a measure, so an amenable group with a
    weakly aperiodic SFT is not in `𝔑`.
  - For non-amenable one-ended groups without `Z^2` (surface groups, cocompact lattices in `Sp(n,1)`), strongly
    aperiodic SFTs are known in the literature for some classes, but this lane found no argument that they carry
    invariant measures. That is where the obstruction currently dies.
- **Minimal-free variant.**
  - `Z^2 × Λ` has minimal free witnesses (Theorem Z.3, a product).
  - `SL_3(Z)`: co-induction gives a non-minimal witness, and a minimal subsystem of the co-induced SFT need not
    carry an invariant measure. Glasner–Weiss style results for Kazhdan groups were not examined.
- **Positive side beyond free groups.** Finite-index induction is the only transfer found. Amalgams over infinite
  subgroups (surface groups) break the integer-flow argument because relators constrain the generator
  permutations jointly.
