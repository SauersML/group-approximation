---
rg: 2
id: leavitt-path-k-theory-over-finite-fields-via-det
kind: claim
title: Over F_q the K-groups of a sinkless sourceless graph algebra vanish exactly when det(1 - N^t) has the right arithmetic
distinct_from:
  ara-cortinas-leavitt-tensor-k-theory-vanishes: that is the vanishing of every K-group of L_2 and L_2 tensor a regular supercoherent ring; this decides vanishing of K_1, K_2 and all higher K-groups for every sinkless sourceless finite graph algebra over a finite field through det(1 - N^t).
  leavitt-tensor-powers-have-trivial-k-theory: that asks about tensor powers of L_2, which are not graph algebras; this settles graph algebras L_(F_q)(E) of one finite graph.
artifacts:
  - research/artifacts/bh-leavitt-path-steinberg-hosts-2026-09-12.md
---

**ESTABLISHED.** Let `q = p^f`, let `E` be a finite graph with no sinks and no
sources and adjacency matrix `N`, and put `D = det(1 - N^t)`. Write
`L = L_(F_q)(E)`.

1. `K_1(L) = 0` iff `D != 0` and `gcd(D, q-1) = 1`.
2. `K_2(L) = 0` iff `gcd(D, q-1) = 1`.
3. `K_n(L) = 0` for every `n >= 1` iff `D = ±p^k` for some `k >= 0`.
4. If `D != 0`, `K_0(L)` has order `|D|`.

**Over `F_2`:**
- `K_2(L) = 0` for every such graph;
- `K_1(L) = 0` iff `D != 0`;
- `L` is K-acyclic in degrees `>= 1` iff `D = ±2^k`.

**Example.** Take two vertices with `N = [[2,3],[1,2]]`. Then:
- `1 - N^t = [[-1,-1],[-3,-1]]`, `D = -2`, `K_0 = Z/2`;
- `[1] = (1,1)` is minus the second column, so `[1] = 0`;
- every `K_n`, `n >= 1`, vanishes over `F_2`.
This is a K-acyclic candidate host that is not isomorphic to `L_2`, since
`K_0(L_2) = 0`. One vertex with `n` loops is K-acyclic over `F_2` iff `n - 1` is a
power of two, but there `[1]` generates `K_0 = Z/(n-1)`.

DERIVATION
leavitt-path-k-theory-det-proof
