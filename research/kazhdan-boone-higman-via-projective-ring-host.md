---
rg: 2
id: kazhdan-boone-higman-via-projective-ring-host
kind: route
title: The rank-four projective elementary host is a quotient of EL_4 over a finitely presented ring, so the projective ring route gives Kazhdan hosts
target: kazhdan-boone-higman-conjecture
requires: [boone-higman-thompson-simple-envelope, clapham-fp-embedding-preserves-word-problem, decidable-group-ring-has-fp-projective-simple-host, projective-elementary-fp-kernel-criterion, ring-elementary-bh-hosts-are-kazhdan]
artifacts:
  - research/artifacts/ring-hosts-are-kazhdan-2026-09-17.md
---

Let `G` be finitely generated with solvable word problem.

1. **Host.** Run `boone-higman-via-projective-ring-host` verbatim. This gives
   an infinite simple `S >= G`, a finitely presented `H >= S` with solvable
   word problem, and a finitely presented ring `L` from
   `decidable-group-ring-has-fp-projective-simple-host`, with
   `G <= S <= PEL_4(L)`. By `projective-elementary-fp-kernel-criterion`,
   `PEL_4(L)` is finitely presented and simple.
2. **(T).** `L` is finitely presented, so it is finitely generated.
   `ring-elementary-bh-hosts-are-kazhdan`(4) says that
   `PEL_4(L) = EL_4(L)/Z(EL_4(L))` has property (T).

Hence `G` embeds in a finitely presented simple Kazhdan group.
