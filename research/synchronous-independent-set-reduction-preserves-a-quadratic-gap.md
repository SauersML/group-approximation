---
rg: 2
id: synchronous-independent-set-reduction-preserves-a-quadratic-gap
kind: claim
title: The independent-set reduction preserves a quadratic gap in the synchronous tracial model
artifacts:
  - research/artifacts/independent-set-rounding-rank-router-2026-08-23.md
distinct_from:
  harris-bisynchronous-game-algebra-preservation: that preserves a synchronous game algebra through an equal-size bisynchronous conversion; this converts soundness to an independent-set game whose loss is a sum of projection overlaps.
  one-gram-vector-decodes-a-finite-bcs-strategy: that reads one BCS strategy from one nontracial Gram vector; this starts with an already synchronous tracial strategy and removes the Boolean predicate entirely.
---

**ESTABLISHED.**  Let `G` be a fixed `t`-question synchronous game and let
`I(G)` be its diagonally weighted `t`-independent-set game.  There is a
universal `zeta>0` such that

```text
omega_s^*(G)<1-epsilon
 => omega_s^*(I(G))<1-zeta epsilon^2/t.                (SIG1)
```

Equivalently, a synchronous tracial strategy for `I(G)` with loss `delta`
decodes a synchronous strategy for `G` with loss `O(sqrt(t delta))`.  This is
the sharp synchronous Lemma 5.1 interface; a group decoder that already
uses one tracial PVM family does not pay the fourth-root conversion needed
for arbitrary nonsynchronous strategies.

Every losing atom of `I(G)` is a forbidden projection overlap and contributes

```text
tau(P_i^uP_j^v)=||P_i^uP_j^v||_2^2.                  (SIG2)
```

Consequently its complete loss is a fixed weighted sum of pairwise overlap
energies.  The source game's arbitrary Boolean acceptance predicate is no
longer part of the groupification interface.

