---
rg: 2
id: nuclear-non-uct-via-infinite-mf-tensor
kind: route
title: A nuclear algebra with a faithful trace and an infinite MF tensor product is not MF, so it fails the UCT
target: nuclear-algebra-without-uct-exists
requires:
  - nuclear-factor-with-infinite-mf-tensor-exists
  - mf-min-tensor-exact-mf-is-mf
  - tww-gabe-schafhauser-af-embedding-theorem
---

Let `A` and `C` be as in the first premise.
1. **C is not MF.** `C` is nuclear, hence exact. If `C` were MF, `A ⊗_min C` would
   be MF and so stably finite (second premise), contradicting the first premise.
2. **C fails the UCT.** Suppose `C` satisfied the UCT. `C` is separable and
   exact, and its faithful trace is amenable because `C` is nuclear. So `C` would
   embed in a unital simple AF algebra (third premise). AF-embeddable algebras
   are quasidiagonal, hence MF, contradicting 1.
