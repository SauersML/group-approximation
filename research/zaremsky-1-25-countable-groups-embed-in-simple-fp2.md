---
rg: 2
id: zaremsky-1-25-countable-groups-embed-in-simple-fp2
kind: claim
title: "Zaremsky Problem 1.25 resolved: does every countable group embed in a simple group of type FP_2?"
root: true
distinct_from:
  countable-group-embeds-in-two-generator-simple-group: that is the classical theorem that every countable group embeds in a finitely generated simple group, with no finiteness condition beyond generation; this is the question whether the simple envelope can also be of type FP_2.
  boone-higman-conjecture: that asks for finitely PRESENTED simple envelopes and so is restricted to finitely generated groups with solvable word problem; this asks for simple envelopes of type FP_2, which carry no computability restriction, and quantifies over all countable groups.
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 1, Problem 25, verbatim:
"(Added 7/12/26) (Llosa Isenrich–Schesler–Wu) Does every countable group embed
in a simple group of type FP2? (Leary proved that every countable group embeds
in a group of type FP2, so this would prove a sort of “FP2 version” of the
Boone–Higman conjecture.)"

This claim is the question. It is established only through an answer route:
- **Yes**: `zaremsky-1-25-by-yes` requires `every-countable-group-embeds-in-a-simple-fp2-group`.
- **No**: `zaremsky-1-25-by-no` requires `some-countable-group-embeds-in-no-simple-fp2-group`.
Never write a `requires: []` route into this claim.

## Precise reading

- `FP_2` means `FP_2` over `Z`: the augmentation ideal of `ZG` is finitely
  presented as a `ZG`-module. Llosa Isenrich–Schesler–Wu state the question
  with `FP_2(Z)`.
- "Simple" means nontrivial with no proper nontrivial normal subgroups.
  Every countable group `H` embeds in `H * Z`, so the input may be assumed
  infinite and finitely generated only after an embedding theorem; the
  question as printed quantifies over all countable groups, and by
  Higman–Neumann–Neumann it is equivalent to the same question for
  2-generator groups.
- Attribution. Zaremsky's list credits Llosa Isenrich–Schesler–Wu. Their
  paper arXiv:2510.01952v1 (2 Oct 2025) prints it as "Question 1.12
  (Zaremsky). Does every countable group embed in a simple group of type
  FP_2(ℤ)?". Credit both.

## What is known (verified sources, see the citation nodes)

- Leary, arXiv:1610.05813v5, Theorem 1.1: every countable group embeds in an
  `FP_2` group.
- Hall and Schupp: every countable group embeds in a finitely generated simple
  group (`countable-group-embeds-in-two-generator-simple-group`).
- Neither construction keeps the other property. For finitely presented
  envelopes the question is Boone–Higman, and Kuznetsov's argument
  (`simple-envelope-forces-solvable-word-problem`) restricts it to inputs with
  solvable word problem. `FP_2` groups need not be recursively presented, so
  that obstruction does not apply here.
- Partial positive classes: every group that embeds in a finitely presented
  simple group (finitely presented implies `FP_2`); every finitely generated
  subgroup of `GL_n(Q)` (Llosa Isenrich–Schesler–Wu, Theorem 1.4); every group
  admitting a faithful action of type `[HA_2]` in the sense of
  Fournier-Facio–Wu–Zaremsky (arXiv:2603.24687v2, Corollary 4.14).
- A yes answer forces continuum many simple `FP_2` groups, some of them not
  recursively presented (a counting argument). That would answer the first
  part of Problem 1.20 and both questions of FFWZ Remark 4.16.

## Attempts

- 2026-09-13 (lane z1-25-fp2-simple-embed): status search found no answer after
  July 12, 2026 (arXiv listing and web search, bounded; no MathSciNet). The
  live route is the twisted Brin–Thompson envelope: a faithful `[HA_2]`
  action of an `FP_2` overgroup of the input gives a simple `FP_2` group
  containing it. The crux is producing such actors for inputs that are not
  recursively presented; see the answer claims.
- 2026-09-17 (sw-118, transplanter, symbolic dynamics): dead envelope family.
  Nekrashevych groups of V-times-subshift groupoids cannot contain every input.
  `v-times-subshift-full-groups-locally-embed-in-v`
  proves that every finitely generated subgroup of `[[G_V x (Z ⋉ Y)]]`, for
  irreducible `Y` (full shift, SFTs, minimal), is locally embeddable into `V`.
  So an infinite finitely presented simple Kazhdan group (the km-246 lattice) is
  in no such host, and neither is any input containing it. The exact break:
  periodic approximations of `Y` turn the generators' finite rules into
  elements of `V_{2,N} ≅ V`, and `V` is Haagerup.
  - The same holds with `Z` replaced by any acting group whose subshift has
    finite approximations (PA*). This covers full shifts over residually finite
    groups. So such hosts need a subshift with no periodic approximations, or an
    acting group with few finite quotients.
