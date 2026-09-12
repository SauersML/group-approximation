---
rg: 2
id: kun-thom-actors-not-virtually-torsion-free-proof
kind: route
title: A finite-index subgroup meets an infinite elementary abelian root subgroup nontrivially
target: kun-thom-actors-have-no-torsion-free-finite-index-subgroups
requires: []
---

Consider the root subgroup `U_12 = {e_12(a) : a in R}`.
- It is isomorphic to `(R,+)`, because `e_12(a) e_12(b) = e_12(a+b)`.
- It is infinite, and each nonzero element has order `p`, because `p a = 0`
  in `R`.

Let `K <= G` have finite index. Then `K cap U_12` has finite index in
`U_12`, so it is infinite. Hence it contains some `e_12(a)` with `a != 0`,
which is an element of order `p`.

For the Theorem E pairs, `R = F_q[x_1^(+-1),...,x_d^(+-1)]` is infinite of
characteristic `p`. QED
