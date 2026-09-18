---
rg: 2
id: irs-surjunctivity-iff-pmp-graphing-surjunctivity
kind: claim
title: The IRS strengthening is equivalent to Gottschalk's conjecture for p.m.p. free-group graphings with measurable tables
distinct_from:
  free-group-irs-carry-no-strict-design: that is the IRS statement itself; this proves it equivalent to a surjunctivity statement for arbitrary p.m.p. actions with measurable local tables, at the cost of extra free generators.
  gottschalk-surjunctivity-conjecture: that concerns cellular automata over a group; this concerns rules on orbit graphs of p.m.p. actions whose tables vary measurably with the point.
  atomic-irs-strict-designs-are-nonsurjunctive-quotients: that decides atomic IRS through normalizer quotients; this covers every IRS, by realizing it as a stabilizer process and colouring orbits.
artifacts:
  - research/artifacts/design-subgroup-tests-2026-09-17.md
---

**ESTABLISHED** by `irs-surjunctivity-iff-pmp-graphing-surjunctivity-proof`.

**GG(r).**
- Setting: `F_r` acts on a standard probability space measure preservingly, not necessarily freely.
- A *measurable-table rule* of radius `R` assigns to each point, measurably, a local map
  `A^{B_R} -> A` applied to the word-indexed values on its orbit ball.
- GG(r) says: if two such rules satisfy `sigma tau = id` on a.e. orbit, then `tau` is onto on a.e. orbit.

**Theorem.**
- GG(r) implies P1(r), which is `free-group-irs-carry-no-strict-design` at rank `r`.
- P1(r + L) implies GG(r) for rule pairs using at most `L` table pairs.
- Hence P1 over all ranks is equivalent to GG over all ranks.

**Supplement** (artifact Proposition 1.2). For a free action of a finitely generated group `G`, a strict
measurable pair whose table process has full support gives a strict cellular automaton over `G`, with alphabet
`T x A`. So `irs-strict-designs-yield-nonsurjunctive-groups` holds for free actions with full-support tables. It
remains open exactly at proper-subshift table processes and at non-free stabilizer processes.
