---
rg: 2
id: tester-host-pos-iff-maximal-bernoulli-rokhlin-entropy
kind: claim
title: The Gottschalk tester host has a positive-entropy free ergodic action iff its Bernoulli shifts have maximal Rokhlin entropy
distinct_from:
  bernoulli-rokhlin-entropy-maximal-on-fixed-tester: that is the open maximality statement for the host; this proves it equivalent to the weaker-looking existence of one positive-entropy free ergodic action of the same host.
  rokhlin-supremum-dichotomy-with-centralized-self-copies: that is the dichotomy for every group containing its own square with unbounded torsion; this is its instance for the fixed tester host, together with the passage of positive entropy to every recursively presented group.
artifacts:
  - research/artifacts/rokhlin-entropy-self-copy-dichotomy-2026-09-12.md
---

Let `U` be the fixed two-generator finitely presented host of `whitehead-universal-finitely-presented-container`. It is also the host of `universal-all-group-subgroup-colimit-class-tester` and `gottschalk-surjunctivity-fixed-two-generator-tester`. Then:

1. `h^Rok_sup(U)` is `0` or `infinity`;
2. POS(`U`), INF(`U`) and RBS(`U`) are equivalent;
3. if POS(`U`) holds, then every infinite countably generated recursively presented group has a free ergodic p.m.p. action with positive Rokhlin entropy.

**Why `U` qualifies.** `U x U` is finitely presented, so it embeds in `U`. And `U` contains a cyclic group of every order. Take `G` to be the first factor of an embedded `U x U`, and `T_n` a cyclic subgroup of order `n` of the second factor.

**Positive entropy passes down (3).** RBS(`U`) gives the Bernoulli 2-shift over `U` Rokhlin entropy `log 2`. Let `K <= U` be infinite. The restriction to `K` is free and mixing, hence ergodic. A partition generating for `K` also generates for `U`, so the Rokhlin entropy for `K` is at least `log 2`. Every countably generated recursively presented group embeds in `U`.

Consequently POS for the single group `U` is equivalent to Seward's hypothesis that every countably infinite group satisfies POS:
- one direction is specialization;
- for the other, POS(`U`) gives RBS(`U`), which gives maximality for every group by `rokhlin-maximality-on-tester-covers-every-group`, and RBS implies POS for each group.
