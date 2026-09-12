---
rg: 2
id: threshold-free-reverse-kleene-higman-proof
kind: route
title: Enumerate a triviality proof, take the recursion fixed point, and apply effective Higman
target: threshold-free-reverse-kleene-higman-diagonal
requires: []
---

From `e`, construct a program `P_e` which computes `S_e,w_e`, enumerates the
relators `R_e`, dovetails all finite normal-closure certificates for
`w_e in <<R_e>>`, and halts when it finds one.  Kleene's recursion theorem
gives `e_*` whose behavior is `P_(e_*)`.

It cannot halt: a found certificate would give `w_(e_*)=1`, while `(TFK1)`
would give `w_(e_*)!=1`.  It also follows directly that `w_(e_*)!=1`, because
if the word were trivial then one finite derivation using finitely many
enumerated relators would eventually make `P_(e_*)` halt.  Hence `(TFK2)`
gives a nontrivial element in `Rad_hyp(Gamma_(e_*))`, so
`Gamma_(e_*)` is non-hyperlinear.

This group is finitely generated and recursively presented.  Effective
Higman embedding puts it inside a finitely presented group `H`.  If `H` were
hyperlinear, its subgroup `Gamma_(e_*)` would be hyperlinear, a contradiction.
