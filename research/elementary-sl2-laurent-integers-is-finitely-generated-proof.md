---
rg: 2
id: elementary-sl2-laurent-integers-is-finitely-generated-proof
kind: route
title: "Diagonal unit matrices are elementary and conjugate E_12(r) to E_12(t^2 r)"
target: elementary-sl2-laurent-integers-is-finitely-generated
requires: []
---

Let `R = Z[t,t^{-1}]` and `S = {E_12(1), E_12(t), E_21(1), E_21(t), D(t)}` with
`D(u) = diag(u, u^{-1})`.

1. **Diagonal units are elementary.** For a unit `u`, put
   `w(u) = E_12(u) E_21(-u^{-1}) E_12(u)`. Multiplying out:
   `E_12(u)E_21(-u^{-1}) = [[0,u],[-u^{-1},1]]`, and then
   `w(u) = [[0,u],[-u^{-1},0]]`. Hence
   `w(u) w(1)^{-1} = [[0,u],[-u^{-1},0]]·[[0,-1],[1,0]] = diag(u, u^{-1}) = D(u)`,
   so `D(u) ∈ E_2(R)`. In particular `S ⊂ E_2(R)`.
2. **Conjugation shifts degrees by two.**
   `D(t^k) E_12(r) D(t^k)^{-1} = E_12(t^{2k} r)` and
   `D(t^k) E_21(r) D(t^k)^{-1} = E_21(t^{-2k} r)` for all `k ∈ Z`.
   So `<S>` contains `E_12(t^{2k})` and `E_12(t^{2k+1})` (conjugate `E_12(1)`,
   `E_12(t)`) and `E_21(t^{2k})`, `E_21(t^{2k+1})` (conjugate `E_21(1)`,
   `E_21(t)` by `D(t^{-k})`), for every `k ∈ Z`.
3. **Additivity.** `E_12(r+s) = E_12(r)E_12(s)`, and every `r ∈ R` is a finite
   `Z`-combination of powers `t^i`, so `E_12(r) = Π_i E_12(t^i)^{c_i} ∈ <S>`;
   likewise `E_21(r)`.

Hence `E_2(R) = <S>`.
