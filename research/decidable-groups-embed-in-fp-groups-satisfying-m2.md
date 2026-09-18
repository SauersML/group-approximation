---
rg: 2
id: decidable-groups-embed-in-fp-groups-satisfying-m2
kind: claim
title: Every finitely generated group with solvable word problem embeds in a finitely presented group with solvable word problem that carries an effectively closed minimal free subshift
distinct_from:
  decidable-fp-groups-have-effective-minimal-free-subshifts: that is (M2) for EVERY infinite fp group with solvable word problem; this asks only for SOME fp decidable overgroup of each input, which is all the master route uses and lets the envelope be modified (for instance to Λ_0 * Z).
  decidable-groups-embed-in-fp-groups-with-minimal-free-sft: that is (P1), asking for a minimal free subshift OF FINITE TYPE on the envelope; this asks only for an effectively closed one.
---

**OPEN.** Route: `m2-envelopes-via-free-product-with-z`.

**Statement.** For every finitely generated `G` with solvable word problem there is a
finitely presented `Λ ⊇ G` with solvable word problem such that `Λ` carries a nonempty
effectively closed subshift on which it acts minimally and freely.

**Why this is the form the master route needs.**
- In `minimal-free-sft-via-plane-constant-minimal-simulation` and the master route
  (`research/artifacts/gq-bh-synthesis-master-route.md`, gate G1/M2), the envelope `Λ_0` is
  only used through three properties: it is finitely presented, has solvable word problem,
  and contains the input.
- So (M2) for one such envelope per input suffices, and the envelope may be changed; for
  instance, replace `Λ_0` by `Λ_0 * Z`.

**Known instances.**
- Inputs that have a finitely presented residually finite overgroup: take that overgroup, by
  `effectively-rf-groups-have-effective-minimal-free-subshifts`. This case is irrelevant to
  Boone–Higman, whose reduced inputs are simple.
- The Boone–Higman-relevant case, simple Kazhdan inputs: open. It reduces to
  `decidable-groups-have-universal-hyperaperiodic-points` for their Clapham envelopes, by the
  route.

**Route fires (2026-09-18, bh-g1-simulation; design level, unreviewed).** The one open premise of
`m2-envelopes-via-free-product-with-z`, `decidable-groups-have-universal-hyperaperiodic-points`,
now has route `universal-hyperaperiodic-points-via-decidable-free-subshifts`. So this statement
holds, with `Λ = A * Z` for the Clapham envelope `A`. The witness is tree-based on the
overgroup. On `A` itself it is a transitive, non-minimal free subshift with decidable language.
