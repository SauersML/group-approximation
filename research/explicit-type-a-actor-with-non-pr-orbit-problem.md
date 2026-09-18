---
rg: 2
id: explicit-type-a-actor-with-non-pr-orbit-problem
kind: claim
title: Some explicitly described finitely presented group has a faithful type (A) action whose orbit problem is not primitive recursive
distinct_from:
  type-a-actors-with-arbitrarily-hard-word-problem: that asks for one actor beyond each recursive bound and is silent on explicitness; this asks for one explicit actor beyond every primitive recursive bound, which is exactly what Kourovka 7.19 needs from the twisted Brin-Thompson branch.
  hard-half-finite-permutations-have-fp-shift-envelopes: that is a sufficient condition inside the strongly shift-similar family, for every recursive bound; an explicit instance of it at a bound dominating all primitive recursive functions would give this claim.
---

**OPEN.** There is an explicitly described finitely presented group `G` with a faithful action on a set `S` of
type (A) (`type-a-action-gives-boone-higman-for-subgroups`) such that the orbit problem `OP(G,S)` of
`twisted-brin-thompson-wp-equals-actor-orbit-problem` is not primitive recursive. The orbit problem is the word
problem of `G` together with membership in point stabilizers of orbit representatives.

**Use.** Route `kourovka-7-19-via-hard-type-a-actor` turns such an actor into an answer to Kourovka 7.19.

**Where hardness may and may not come from.**
- *Not from base points of prefix-replacement hosts:*
  `aperiodic-point-stabilizers-in-germ-extensions-of-v-are-not-fg`.
- *Not from single-machine singular schedules:* `block-power-germ-schedules-with-fp-germ-group-are-exponential`.
- *Not from bounded-displacement half-finite generators:* the bounded-displacement theorem on
  `hard-half-finite-permutations-have-fp-shift-envelopes`.
- *Possible sources left:*
  - unbounded-displacement half-finite generators pinned by a finite cross-scale rule (Attempt 6 there);
  - singular germ transports between different `V`-orbits (Attempt 4 on
    `fp-simple-groups-with-arbitrarily-complex-word-problem`);
  - normalizing permutations (Attempt 5 on `type-a-actors-with-arbitrarily-hard-word-problem`).
