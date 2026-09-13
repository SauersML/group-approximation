---
rg: 2
id: no-fp-infinite-simple-group-is-amenable
kind: claim
title: Every finitely presented infinite simple group is non-amenable
refuted_by:
  - fp-infinite-simple-amenable-group
distinct_from:
  fp-infinite-simple-amenable-group: that is the existence claim; this is its negation, which would answer Zaremsky Problem 1.10 negatively
  periodic-approximable-subshifts-host-no-fp-simple-group: that removes one class of hosts, full groups of periodically approximable subshifts; this is the universal statement over all finitely presented infinite simple groups
---

**OPEN.** No finitely presented infinite simple group is amenable.

This is the negation of `fp-infinite-simple-amenable-group`. It would answer
Zaremsky Problem 1.10 negatively, through `zaremsky-1-10-by-nonexistence`.

## Attempts

- **Partial no-gos on main.** Each removes a class of groups or hosts; none is
  universal.
  - `amenable-full-group-forces-invariant-measure`: compressible groupoids and
    every host containing Thompson's `V`.
  - `periodic-approximable-subshifts-host-no-fp-simple-group`: subgroups of full
    groups of minimal `Z`-subshifts, including the Juschenko–Monod groups.
  - `residually-finite-minimal-actions-have-lef-full-groups` with
    `finitely-presented-lef-groups-are-residually-finite`: full groups of minimal
    topologically free residually finite actions.
  - `zd-derived-full-group-fp-forces-finite-type`: derived full groups of free
    minimal `Z^d`-subshifts that are not of finite type.
  - `amenable-infinite-simple-circle-groups-fix-a-point`: infinite simple groups
    acting on the circle without a global fixed point. This includes 1-periodic
    simple groups of line homeomorphisms whose circle action has no fixed point, such
    as Hyde–Lodha's `Q_2` (`hyde-lodha-periodic-simple-groups-are-not-amenable`).
  - `amenable-fg-simple-groups-are-not-left-orderable`: every finitely generated
    infinite simple group with a nontrivial action on the line or the circle, through
    Witte Morris's theorem.
- **Isolation.** A finitely presented infinite simple group is an isolated point
  of the space of marked groups, so it is not a limit of finite groups. Amenability
  supplies Følner sets, not marked approximants, and no contradiction between the
  two is known.
- 2026-09-13: the nonexistence side is worked by lane z1-10-simple-amen-block.
