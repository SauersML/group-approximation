---
rg: 2
id: hyperlinear-fp-infinite-simple-group
kind: claim
title: Some finitely presented infinite simple group is hyperlinear
root: true
distinct_from:
  fp-simple-nonsofic-group: That asks for a finitely presented simple group which is NOT sofic; this asks for one which IS hyperlinear. The two are compatible, since a hyperlinear nonsofic simple group would satisfy both.
  leavitt-hyperlinear-branch-implies-thompson-v-hyperlinear: That records that the Leavitt hyperlinear branch would make Thompson's V hyperlinear; this is the existence question for any finitely presented infinite simple group, of which V is one candidate.
  nonhyperlinear-existence-is-two-generator-simple: That reduces the existence of a nonhyperlinear group to simple groups with arbitrary presentations; this asks for a positive certificate for a finitely presented simple group.
  fournier-facio-simple-factor-not-hyperlinear: That is the negative assertion for the specific simple factor of the Fournier--Facio construction; this is the positive existence statement over all finitely presented infinite simple groups.
---

**OPEN.**  There exists a finitely presented infinite simple group `S` whose
group von Neumann algebra embeds in `R^omega`, i.e. `S` is hyperlinear.
Preferred strengthenings, in order: `S` torsion-free; `S` sofic.

**Why it matters.**
- It is gate 1 of the positive branch for the Fournier--Facio group:
  `fournier-facio-nontrivial-quotients-contain-simple-wreath` makes any
  hyperlinear nontrivial quotient contain its simple factor.
- The same gate appears for the Leavitt fork through Thompson's `V`.
- A finitely presented infinite simple group is not residually finite and
  not LEF, so every known soficity or hyperlinearity certificate that runs
  through finite or amenable quotients fails for it.

**Evidence that it is open (not a complete literature verification).**
- Salo, arXiv:2103.15505 (abstract): resolving soficity of mapping class
  groups of mixing SFTs "in either direction would solve an open problem in
  geometric group theory", because Thompson's `V` embeds there.  So the
  soficity of `V` was open in 2021.
- `fp-simple-nonsofic-group` lists every Thompson-like finitely presented
  simple group in this graph with unknown sofic status.
- Arxiv abstract searches (sofic AND simple AND presented; hyperlinear AND
  simple; sofic AND Thompson; sofic AND lattice AND trees) returned no claim
  of such an example.

## Attempts

- **Limits in the space of marked groups.**  Dead: a finitely presented
  simple group is isolated, so it is a limit of hyperlinear groups only if it
  is hyperlinear.  See `fp-simple-groups-escape-soft-hyperlinear-permanence`.
- **Residual amenability, LEA, LEF.**  Dead: a residually amenable infinite
  simple group is amenable, and a finitely presented LEA group is residually
  amenable.  No finitely presented infinite simple amenable group is recorded
  here.
- **Amenable-edge tree splitting.**  Live.  A finite graph of hyperlinear
  groups over amenable edge groups is hyperlinear
  (`amenable-edge-graph-corners-cannot-groupify-a-nonce-game`).  Le Boudec's
  finitely generated simple groups with locally finite vertex stabilizers show
  the route produces simple groups, but those are not finitely presented; see
  `fg-simple-hyperlinear-tree-group-not-finitely-presented`.  The remaining
  demand is a finitely presented example, which forces finitely generated
  amenable edge groups and finitely presented vertex groups.
