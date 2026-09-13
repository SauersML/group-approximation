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
artifacts:
  - research/artifacts/zp-fp-simple-amenable-obstructions-2026-09-13-part1.md
  - research/artifacts/zp-fp-simple-amenable-obstructions-2026-09-13-part2.md
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
  - `fp-alternating-full-groups-of-free-subshifts-force-sft` (unreviewed): the same
    over every infinite finitely generated group, without minimality, for the derived
    and alternating full groups and every finitely presented subgroup containing the
    rule 3-cycles. So a full-group example over a free subshift needs a nonempty
    strongly aperiodic SFT.
  - `circle-rotation-zd-derived-full-groups-are-not-fp` (unreviewed): free
    `Z^d`-actions on the circle by rotations, coded by interval partitions, are never
    of finite type. This covers the free rank-2 interval exchange realizations.
  - `amenable-infinite-simple-circle-groups-fix-a-point`: infinite simple groups
    acting on the circle without a global fixed point. This includes 1-periodic
    simple groups of line homeomorphisms whose circle action has no fixed point, such
    as Hyde–Lodha's `Q_2` (`hyde-lodha-periodic-simple-groups-are-not-amenable`).
  - `amenable-fg-simple-groups-are-not-left-orderable`: every finitely generated
    infinite simple group with a nontrivial action on the line or the circle, through
    Witte Morris's theorem.
  - `fg-infinite-simple-groups-are-not-elementary-amenable`: elementary amenable
    groups (Chou 1980).
  - `fg-simple-projective-interval-groups-are-trivial`: subgroups of `F`,
    `PL_+[0,1]` and piecewise-projective groups of a compact interval.
  - `fp-simple-groups-have-no-interval-exchange-action`: every group of interval
    exchanges, through LEF by rational specialisation, including the amenable rank-2
    interval exchange groups and their non-free realizations.
- **Census.** Every candidate class with its killing reason is tabulated in the
  part 1 artifact, Section 1. Three classes are live:
  - free minimal SFTs over one-ended amenable groups (Labbé, Penrose);
  - non-free or non-expansive groupoid hosts;
  - candidates with no dynamical model.
- **Word problem of the acting group (remark, not a node).** Jeandel,
  arXiv:1501.06831, abstract: a finitely presented group with a strongly aperiodic SFT
  has decidable word problem. With Theorem G, full groups over free subshifts of
  finitely presented acting groups with undecidable word problem are dead. Only the
  abstract was read.
- **Isolation.** A finitely presented infinite simple group is an isolated point
  of the space of marked groups, so it is not a limit of finite groups. Amenability
  supplies Følner sets, not marked approximants, and no contradiction between the
  two is known.
- 2026-09-13: the nonexistence side is worked by lane z1-10-simple-amen-block.
