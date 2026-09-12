---
rg: 2
id: decidable-groups-embed-in-rover-nekrashevych-hosts
kind: claim
title: Every decidable finitely generated group embeds in a finitely presented simple Rover--Nekrashevych commutator subgroup
distinct_from:
  boone-higman-conjecture: that allows any finitely presented simple host; this requires the host to be a finitely presented simple commutator subgroup [V_d(H),V_d(H)] of the Rover--Nekrashevych group of a self-similar group H, the host shape of Zaremsky's theorem.
  every-decidable-group-embeds-in-fp-self-similar-group: that asks for a self-similar host and is refuted because such hosts are residually finite; this asks for a Rover--Nekrashevych commutator host, which contains Thompson's V and so is not excluded by residual finiteness.
  fp-self-similar-groups-embed-in-fp-simple-groups: that embeds finitely presented self-similar groups themselves; this asks to embed arbitrary decidable inputs, including infinite simple ones, in hosts of the same shape.
---

**OPEN.** For every finitely generated group `G` with solvable word problem
there are `d >= 2`, a self-similar group `H <= Aut(T_d)` and an embedding of `G`
into `[V_d(H),V_d(H)]`, where this commutator subgroup is finitely presented and
simple.

## Why this shape

- It implies `boone-higman-conjecture` at once, by the route
  `boone-higman-via-rover-nekrashevych-hosts`.
- It is the only way the self-similar method can reach the general conjecture.
  Self-similar hosts contain only residually finite groups
  (`self-similar-hosts-contain-only-residually-finite-groups`), while
  `[V_d(H),V_d(H)]` contains copies of V and is not residually finite.
- Finite presentation of the host is part of what has to be proved. The abstract
  of Zaremsky arXiv:2405.09722, read on MSI 2026-09-12: "The simple groups in
  question are certain commutator subgroups of Röver-Nekrashevych groups, and
  the difficulty lies in the fact that even if a Röver-Nekrashevych group is
  finitely presented, its commutator subgroup might not be."

## Necessary conditions on a host

- **(R1) Hard nucleus.** The word problem of `V_d(H)` reduces to that of `H` at
  exponential cost (`rover-nekrashevych-word-problem-reduces-to-self-similar-group`),
  and word-problem bounds pass from a host to its finitely generated subgroups.
  So inputs beyond a recursive bound force `H` beyond a comparable bound, a
  family as in `fp-self-similar-groups-with-arbitrarily-hard-word-problem`.
- **(R2) Piecewise-germ action.** `G` must act faithfully on the boundary of
  `T_d` by homeomorphisms that are locally a prefix replacement followed by an
  element of `H`. For an infinite simple input this action inherits no finite
  quotient from `H`.
- **(R3) Interface.** Such a host is a finitely presented group of Cantor-space
  homeomorphisms containing standard V. According to the lane
  `bh-twisted-brin-thompson`, those carry type (A) actions
  (`fp-full-binary-cantor-groups-have-type-a-actions`), so a host of this shape
  also feeds the twisted Brin--Thompson route.

## Attempts

1. **Self-similar hosts.** Dead: `every-decidable-group-embeds-in-fp-self-similar-group`
   is refuted.
2. **Simple envelope first.** `boone-higman-thompson-simple-envelope` embeds `G`
   in an infinite finitely generated computably presented simple group `S`. The
   task becomes a faithful piecewise-`H` action of `S` on Cantor space, with the
   commutator host finitely presented. This is stated, not carried out: no
   candidate `H` is known for any infinite simple `S` beyond V-like groups.
