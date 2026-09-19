---
rg: 2
id: free-label-erasure-calculation-proof
kind: route
title: Factor every labeled word and cancel the labels explicitly
target: free-label-orthogonalization-erases-payload-trace
requires: []
---

For a reduced word `w`, tensor multiplication gives
`w(V)=w(u) tensor lambda(w)`.  The canonical free-group trace of
`lambda(w)` is zero, proving `(FLO2)`.  The resulting homomorphism from
`L(F_r)` to `W*(V_i)` preserves its faithful canonical trace and is therefore
injective as well as surjective.

After adjoining `L_i`, both `u_i tensor 1=V_iL_i^*` and
`1 tensor lambda(s_i)=L_i` belong to the generated algebra.  These two
commuting families generate `M bar tensor L(F_r)`, proving `(FLO4)` and the
mixed-word trace calculation.  This establishes both sides of the no-go.

