---
rg: 2
id: map-matricial-stability-non-mf-proof
kind: route
title: Stable plus no finite-dimensional representations forces every model to be trivial
target: map-matricial-stability-non-mf
requires: []
---

## Why sufficient

Suppose `G` were MF.  By the coordinate presentation
(`countable-group-mf-conventions`) there is an asymptotic homomorphism
`phi_n : G -> U(k_n)` with `‖phi_n(g) phi_n(h) - phi_n(gh)‖ -> 0` and, for
each `s != 1`, `limsup ‖phi_n(s) - 1‖ >= c_s > 0`.

Matricial stability supplies genuine homomorphisms `pi_n : G -> U(k_n)` with
`‖phi_n(s) - pi_n(s)‖ -> 0` for every `s`.  Each `pi_n` is a
finite-dimensional unitary representation of `G`, so minimal almost
periodicity makes it trivial: `pi_n(s) = 1` for all `s` and all `n`.
Therefore `‖phi_n(s) - 1‖ -> 0` for every `s`, contradicting separation at
any `s != 1`.  Since `G` is infinite such an `s` exists.  So `G` is not MF.

Two remarks on scope.  The hypothesis is stability for **all** asymptotic
homomorphisms, not merely separating ones, which is how Dadarlat states it
and is what the argument uses — the model produced by MF-ness is separating,
but stability is applied to it as an arbitrary asymptotic homomorphism.  And
the conclusion is the strong one: not merely that no separating model
exists, but that every corona representation is trivial, so the whole group
lies in the MF radical.
