---
rg: 2
id: osajda-decidable-nonexact-group-satisfies-boone-higman
kind: claim
title: The decidable residually finite non-exact Osajda group embeds in a finitely presented simple group
distinct_from:
  decidable-residually-finite-non-exact-group-exists: that constructs the input group G and proves its word problem solvable; this is the Boone--Higman embedding question for that one explicit input.
  fp-simple-nonexact-group: that asks for any finitely presented simple non-exact group; this node implies it, since exactness passes to subgroups, but it asks for a host containing one specific non-exact group.
  exactness-separates-boone-higman-iff-fp-simple-groups-exact: that shows Boone--Higman fails if every finitely presented simple group is exact; this names the concrete input on which that separation would bite.
artifacts:
  - research/artifacts/gq-bh-bh-testcases-ranking.md
---

**OPEN.** Let `G` be the finitely generated, residually finite, non-exact group
with solvable word problem of `decidable-residually-finite-non-exact-group-exists`,
item 1 (Osajda's graphical small cancellation group on a recursive input
sequence). Then `G` embeds in a finitely presented simple group.

**Why it is a canonical test case.** Exactness (property A) passes to subgroups.
So any host of `G` is a finitely presented simple group without property A, and
this node implies `fp-simple-nonexact-group` (OPEN). Conversely, by
`exactness-separates-boone-higman-iff-fp-simple-groups-exact`, if every finitely
presented simple group were exact, `G` would refute Boone--Higman. So `G` is
exactly where Boone--Higman meets the exactness question.

## Hosts that cannot work

- **Linear hosts.** Finitely generated linear groups are exact
  (Guentner--Higson--Weinberger; textbook, not pinned here). So `G` is not
  linear, although it is residually finite.
- **Hyperbolic and cubulated hosts.** Hyperbolic groups, and groups acting
  properly on finite-dimensional CAT(0) cube complexes, are exact (textbook, not
  pinned here).
- **Amenable-orbit hosts.** Any group with an amenable action on a compact space
  is exact, so no host can act amenably on a compact space.
- **Every standard finitely presented simple group, as far as the graph knows.**
  The exactness of Thompson's `T` and `V`, of `nV`, and of Röver--Nekrashevych
  groups is unknown here (`fp-simple-nonexact-group`, "What is known"). A host
  from this list would have to be shown non-exact first.

What residual finiteness leaves open: unlike the Higman group or the
Baumslag--Gersten group, `G` is residually finite, so self-similar hosts are not
excluded by `self-similar-hosts-contain-only-residually-finite-groups`. But any
self-similar host would itself have to be non-exact.

## Attempts

None yet. The conjecture-free route `fp-simple-nonexact-group-via-free-algebra-linear-groups`
reaches a finitely presented simple non-exact group if
`binary-free-algebra-linear-group-nonexact` holds, but that host is built from a
different non-exact group. Whether it contains `G` is not addressed.
