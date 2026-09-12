---
rg: 2
id: complexity-bounded-host-classes-are-not-universal
kind: claim
title: No class of groups with one recursive word-problem time bound contains every decidable input
distinct_from:
  decidable-fp-groups-need-not-embed-in-rational-group: that treats rational homeomorphism hosts, a single-exponential bound and a finitely presented residually finite input; this treats every class of hosts sharing any recursive time bound, with a two-generated input built here.
  rational-homeomorphism-subgroups-have-exponential-wp: that proves a word-problem bound for one class of hosts; this is the general principle turning any such bound into a non-universality theorem.
artifacts:
  - research/artifacts/boone-higman-self-similar-and-complexity-2026-09-11.md
---

**ESTABLISHED.** Let `T: N -> N` be recursive and let `K` be a class of
finitely generated groups such that every `S in K` has, for some finite
generating set, a word-problem algorithm running in time
`C_S*T(C_S*l) + C_S*l + C_S`. Then some two-generated group with solvable
word problem embeds in no member of `K`.

In particular no class of finitely presented simple groups whose word
problems share one recursive time bound is a universal Boone--Higman
container. Examples of classes this rules out, for the bound `T(l) = 2^l`,
are the finitely generated groups of rational homeomorphisms
(`rational-homeomorphism-subgroups-have-exponential-wp`), including
contracting rational similarity groups and automaton groups. For the bound
`T(l) = 2^(2^l)` it rules out every class whose word problems are uniformly
in doubly exponential time.

Consequently a universal construction must use the input's word-problem
algorithm in a way that makes the host's word problem at least as hard. This
is the complexity form of `compilers-cannot-drop-the-decidability-hypothesis`.

DERIVATION
complexity-bounded-host-classes-are-not-universal-proof
