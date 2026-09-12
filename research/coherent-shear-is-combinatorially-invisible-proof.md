---
rg: 2
id: coherent-shear-is-combinatorially-invisible-proof
kind: route
title: Evaluate the swap penalty on the sheared product state and use exchangeability at the endpoints
target: coherent-shear-is-combinatorially-invisible
requires: []
---

**(i)**  For unit vectors `v, w`, expanding on the symmetric and
antisymmetric subspaces gives

```text
<v tensor w| (I - SWAP)/2 |v tensor w> = (1 - |<v,w>|^2)/2.
```

With `<v_t, v_(t+1)> = cos(theta/D)`, each term contributes
`sin^2(theta/D)/2`, and there are `D` of them, giving (CSI3); the final bound
uses `sin x <= x`.

**(ii)**  `ker h_t` is the symmetric subspace of qubits `t, t+1` tensored
with the rest, and `Tr(h_t sigma) = 0` with `h_t, sigma >= 0` forces
`h_t sigma = 0`, i.e. `ran(sigma)` inside that kernel.  Intersecting over a
block of consecutive indices, `ran(sigma)` lies in the joint kernel of the
adjacent transposition penalties on that block, which is the symmetric
subspace of the block: the adjacent transpositions generate the full
symmetric group, so a vector fixed by each of them is fixed by every
permutation of the block.  A state supported there is invariant under those
permutations, hence its single-qubit marginals inside the block are all
equal.

**(iii)**  The endpoint marginals of `rho_D` are the pure states `|v_0>` and
`|v_D>` with `|<v_0, v_D>| = cos theta`, so their trace distance is
`2 sin theta > 0`.  If `S` were empty, (ii) would make the two marginals of
`sigma_S` equal, and endpoint faithfulness would make them equal to
`|v_0><v_0|` and `|v_D><v_D|` respectively -- a contradiction.  Hence
`|S| >= 1` for every outcome, so `E|S| >= 1`, and the cost clause
`E|S| <= C sum_t Tr(h_t rho_D)` together with (CSI3) forces
`C >= 1/(theta^2/(2D)) = 2D/theta^2`, which is (CSI4).
