---
rg: 2
id: sl2-laurent-integers-fg-iff-gamma0-t-in-fg-subgroup
kind: claim
title: "SL_2(Z[t,t^-1]) is finitely generated iff Gamma_0(t) lies in a finitely generated subgroup of it"
---

Let `R = Z[t,t^{-1}]`, `G = SL_2(R)`, `w = [[0,1],[-1,0]]`,
`w' = [[0,t^{-1}],[-t,0]]`, and `Gamma_0(t) ⊂ SL_2(Z[t])` the matrices whose
lower-left entry is divisible by `t`. Then:

1. `G = <Gamma_0(t), w, w'>`.
2. `G` is finitely generated if and only if there is a finite set `F ⊂ G` with
   `Gamma_0(t) ⊂ <F>`; equivalently, iff there is a finite `F ⊂ G` with
   `SL_2(Z[t]) ⊂ <E_2(R) ∪ F>`.
3. `G = E_2(R)` if and only if `SL_2(Z[t]) ⊂ E_2(R)`, if and only if
   `Gamma_0(t) ⊂ E_2(R)`.

So Problem 3.3 is a question about the level-`t` subgroup `Gamma_0(t)` of
`SL_2(Z[t])`: which of its elements can be written with finitely many extra letters
over the elementary matrices of the Laurent ring. Note that `SL_2(Z[t])` itself is
not finitely generated (it surjects onto `SL_2(F_2[t])`), so the generating set must
use negative powers of `t` essentially.

Proof in `sl2-laurent-integers-fg-iff-gamma0-t-in-fg-subgroup-proof`.
