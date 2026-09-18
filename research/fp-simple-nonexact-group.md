---
rg: 2
id: fp-simple-nonexact-group
kind: claim
title: Some finitely presented simple group is not exact
distinct_from:
  fp-simple-nonsofic-group: that asks for a finitely presented simple nonsofic group and is established through the Leavitt unit group; this asks for failure of property A, which is independent of soficity as far as is known, and no finitely presented simple witness is known.
  exactness-separates-boone-higman-iff-fp-simple-groups-exact: that is the separator theorem showing Boone--Higman implies this; this is the open existence statement, whose refutation would refute the conjecture.
  some-simple-kazhdan-lef-groups-are-not-exact: that gives non-exact simple groups that are finitely generated, with no presentation control; this asks for a finite presentation.
  decidable-residually-finite-non-exact-group-exists: that gives a decidable non-exact group and a decidable non-exact simple Kazhdan LEF group; this asks for a finitely presented simple non-exact group.
artifacts:
  - research/artifacts/exactness-boone-higman-separator-2026-09-17.md
---

**OPEN.** There is a finitely presented simple group without property A, equivalently one whose reduced C*-algebra is not exact.

**Why the graph carries it.** By `exactness-separates-boone-higman-iff-fp-simple-groups-exact`, `boone-higman-conjecture` implies this statement, through route `fp-simple-nonexact-group-via-boone-higman`. So a refutation of this claim refutes the conjecture. A refutation means proving that every finitely presented simple group is exact.

**What is known.**
- **Non-exact, not finitely presented.** Non-exact groups that are finitely generated, simple, Kazhdan, LEF and have solvable word problem exist (`decidable-residually-finite-non-exact-group-exists`).
- **Non-exact, not simple.** Non-exact finitely presented groups exist: Sapir, arXiv:1103.3873, read through its abstract only, gives a closed aspherical 4-manifold group that coarsely contains an expander (artifact §1.4).
- **Simple, finitely presented, exactness unknown.** No finitely presented simple group is known in this graph to be non-exact. The standard finitely presented simple groups have unknown exactness status here: Thompson's `T` and `V`, `nV`, the twisted Brin--Thompson groups `SV_G`, and the Leavitt unit group `L_(F_2)(1,2)^x`.

**Where the difficulty is.** Property A fails through coarsely embedded large-girth graphs or expanders. So a witness needs finitely many relators and simplicity, together with such geometry. The Boone--Higman route supplies it only by embedding a non-exact decidable group. Twisted Brin--Thompson groups `SV_G` contain `G`. So a finitely presented non-exact actor with a type (A) action gives a witness through `type-a-action-gives-boone-higman-for-subgroups`. That reduces this claim to the existence of a non-exact actor, a special case of `permutational-boone-higman-conjecture` for one input.

## Attempts

1. **Through Boone--Higman (c-pz3, swarm-0917, 2026-09-18).** *Conditional.* This holds if `boone-higman-conjecture` holds. No unconditional witness was found.
