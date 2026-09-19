---
rg: 2
id: leavitt-rank-three-unit-lift-proof
kind: route
title: Push the generator through the self-similarity and split the matrix into three units
target: leavitt-rank-three-unit-lift
requires: []
artifacts:
  - GroupApproximation/Leavitt/LeavittSelfSimilarity.lean
  - research/artifacts/kaplansky-direct-finiteness-audit-2026-08-17.md
---

## Direct proof

**Self-similarity.**  With `S = [s_0  s_1]` (a row) and `T = [t_0 ; t_1]` (a
column) the relations read `ST = 1` and `TS = I_2`, so

    Psi : M_2(R) -> R,  Psi(M) = S M T          Phi : R -> M_2(R),  Phi(r) = T r S

are mutually inverse ring isomorphisms: `Psi(Phi(r)) = (ST) r (ST) = r` and
`Phi(Psi(M)) = (TS) M (TS) = M`.  This is `binaryMatrixRingEquiv` in
`GroupApproximation/Leavitt/LeavittSelfSimilarity.lean`, kernel-checked, so
only the matrix splitting below is new here.

**The two images.**  `Phi(r)_(ij) = t_i r s_j`, and associativity alone gives

    Phi(t_0) = [[t_0, 0], [t_1, 0]],        Phi(s_0) = [[s_0, s_1], [0, 0]],

since `t_i t_0 s_j = t_i (t_0 s_j) = delta_(0j) t_i` and
`t_i s_0 s_j = (t_i s_0) s_j = delta_(i0) s_j`.

**Three units per matrix.**  Over a ring of characteristic two,

    [[x,y],[z,w]] = [[1+yz, y],[z,1]] + [[x+1+yz, 1],[1,0]] + [[0,1],[1,w+1]],

checked entrywise (`(1,1)`: `1+yz + x+1+yz = x`; `(1,2)`: `y+1+1 = y`;
`(2,1)`: `z+1+1 = z`; `(2,2)`: `1 + w+1 = w`).  All three summands are units:
the first factors as `[[1,y],[0,1]] [[1,0],[z,1]]`, and for any `c, d`

    [[d,1],[1,0]]^-1 = [[0,1],[1,d]],       [[0,1],[1,c]]^-1 = [[c,1],[1,0]],

the cross terms being `d + d = 0` and `c + c = 0`.

**Specialize.**  For `Phi(t_0)`, `(x,y,z,w) = (t_0, 0, t_1, 0)`; for
`Phi(s_0)`, `(x,y,z,w) = (s_0, s_1, 0, 0)`:

    Phi(t_0) = [[1,0],[t_1,1]] + [[t_0+1,1],[1,0]] + [[0,1],[1,1]],
    Phi(s_0) = [[1,s_1],[0,1]] + [[s_0+1,1],[1,0]] + [[0,1],[1,1]].

Within each line the three matrices are pairwise distinct with no hypothesis
on `R` beyond `1 != 0`: entry `(1,2)` separates the first from the second,
entry `(1,1)` separates the first from the third, and entry `(2,2)` separates
the second from the third.

Transport through the injective `Psi` to get distinct units
`u_i = Psi(U_i)`, `v_i = Psi(V_i)` of `R` summing to `t_0` and `s_0`.  Passing
to `F_2[R^x]` and applying `pi` gives the two support-three lifts.  (The third
unit is shared, `u_3 = v_3`, which affects nothing.)
