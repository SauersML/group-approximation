---
rg: 2
id: measure-rf-class-is-exactly-virtually-free-groups
kind: claim
title: A finitely generated group has all its full-support invariant-measure Cantor actions residually finite iff it is virtually free
artifacts:
  - research/artifacts/un-rf-beyond-free-2026-09-13-part2.md
  - research/artifacts/un-class-n-conjecture-2026-09-13-part1.md
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
- **Exact reduction (un-class-n-conjecture, 2026-09-13, unreviewed).**
  - `measure-rf-class-iff-measured-subshifts-window-periodic`: `Γ ∈ 𝔑` iff every subshift with a full-support
    invariant measure has, at every window, finite-orbit window models realizing all of its patterns.
  - `class-n-groups-have-periodic-points-in-measured-sfts`: so the "only if" direction of the conjecture for a
    non-virtually-free group needs a *measured* SFT without periodic points, or more generally a measured subshift
    whose window SFTs lack covering periodic points.
  - `amenable-weakly-aperiodic-sft-groups-are-not-in-class-n` makes the amenable bullet above a node.
  - **Candidate non-member without `Z^2`: `BS(1,n)`.** Aubrun–Kari report weakly aperiodic SFTs on Baumslag–Solitar
    groups (recalled, not imported: the arXiv API was unreachable from MSI on 09-13), and `BS(1,n)` is amenable. An
    import would put `BS(1,n) ∉ 𝔑`, consistent with the conjecture.
- **Quotient firewall.** `surface-group-pullbacks-of-measured-z2-actions-are-rf`: pulling Labbé's non-RF system back
  to a surface group along a handle retraction gives an RF action. The `Z^2` obstruction transfers along
  subgroups (Proposition R) but not along quotient maps, so surface groups need an intrinsic measured aperiodic SFT.
- **Minimal-free variant.**
  - `Z^2 × Λ` has minimal free witnesses (Theorem Z.3, a product).
  - `SL_3(Z)`: co-induction gives a non-minimal witness, and a minimal subsystem of the co-induced SFT need not
    carry an invariant measure. Glasner–Weiss style results for Kazhdan groups were not examined.
  - A conditional minimal free witness for `SL_3(Z)` via a regular Toeplitz point of the co-induced aperiodic SFT
    along the congruence chain is in `un-class-n-conjecture` artifact part 2.
- **Positive side beyond free groups.** Finite-index induction is the only transfer found. Amalgams over infinite
  subgroups (surface groups) break the integer-flow argument because relators constrain the generator
  permutations jointly. A spare handle acting trivially at the coarse scale absorbs the relator defect
  (squares are commutators after doubling), but a general surface-group action has no such handle.
