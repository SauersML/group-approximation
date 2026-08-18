---
rg: 2
id: boone-higman-thompson-simple-envelope
kind: claim
title: Every finitely generated group with solvable word problem embeds in a finitely generated computably presented simple group
distinct_from:
  simple-envelope-forces-solvable-word-problem: that is the converse direction and needs the envelope to be finitely PRESENTED; this is the forward direction and delivers only a computably presented one. Together they are the Boone-Higman theorem, and neither half implies the other.
  novikov-boone-fp-group-undecidable-word-problem: that exhibits a finitely presented group whose word problem is undecidable; this embeds groups whose word problem IS decidable, and by the converse direction the two statements are about disjoint classes of groups.
  boone-final-group-finitely-presented: that is finite presentability of one specific HNN tower's final group; this is a universal embedding theorem whose envelope is simple and deliberately NOT finitely presented.
  countable-group-embeds-in-two-generator-simple-group: that is Schupp's theorem, which embeds EVERY countable group and gets two generators but no effectivity at all -- the envelope need not be computably presented; this one hypothesizes a solvable word problem and buys computable presentability with it, which is the property Higman's theorem consumes and Schupp's envelope cannot supply.
  boone-higman-conjecture: that demands a finitely PRESENTED simple envelope and is open; this delivers a finitely generated COMPUTABLY presented one and is a theorem. The whole conjecture is the gap between the two adjectives.
  simple-sofic-total-mf-radical: that is about a simple sofic group with a prescribed MF radical, an approximation property; this is a classical effective embedding theorem with no approximation content.
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
---

A finitely generated group has solvable word problem if and only if it embeds
into a finitely generated, computably presented simple group.

Boone--Higman (1974) for the computably presented form; Thompson (1980) for
the finite-generation refinement.

**Verification status.**  Read from source 2026-08-17 in
Belk--Bleak--Matucci--Zaremsky, arXiv:2306.16356 (last revised 22 May 2025),
which states it as Theorem 3.8: "A finitely generated group has solvable word
problem if and only if it embeds into a finitely generated, computably
presented simple group."  Their Theorem 3.6 is the Boone--Higman form without
finite generation.  The primary papers were not re-read.

## Why the exact adjectives matter downstream

`chatterji-kassabov-normal-generator-embedding` consumes *finitely generated
and recursively presented* and nothing else.  Theorem 3.8 delivers exactly
that pair, so the two theorems compose with no gap and no side condition —
which is the only reason the near-solution of
`proper-normal-subgroups-miss-the-normally-generating-core` exists at all.

Two refinements are free and are used:

* The envelope may be taken **infinite**.  Replace the input `G` by
  `G × Z` before applying the theorem: still finitely generated, still
  solvable word problem, still contains `G`, and the resulting simple group
  contains an infinite cyclic subgroup.  An infinite simple group is
  nonabelian, hence perfect.
* The envelope has **decidable word problem**, by the same two-enumeration
  argument as `simple-envelope-forces-solvable-word-problem-proof` run
  against a computable presentation: enumerate proofs of triviality against
  enumerated proofs that the normal closure contains a fixed known
  nontrivial element.
