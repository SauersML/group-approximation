---
rg: 2
id: doubled-odd-iwahori-square-proof
kind: route
title: Pair the even product cycles and take odd-cycle square roots
target: doubled-odd-amplification-erases-iwahori-parabolic-defect
requires: []
---

Consider one cycle of `s` of odd length `m`.  On the sheet fixed by `tau`,
`tau x s` has one `m`-cycle.  On the two sheets exchanged by `tau`, it has
one `2m`-cycle: a return must use an even number of steps and a multiple of
`m`, hence (because `m` is odd) first occurs after `2m` steps.

After taking two copies, every `m`-cycle occurs twice and every `2m`-cycle
occurs twice.  Each odd `m`-cycle has a square root on its own (raise it to
the inverse of `2 modulo m`).  A pair of `2m`-cycles is the square of one
`4m`-cycle: squaring an even cycle splits it into the two cycles on its odd
and even positions.  Performing these constructions independently for all
cycles gives `Q in Sym(Omega)` with

```text
Q^2=P.
```

For the arithmetic realization, take the regular action of an odd
congruence quotient `PSL_2(F_p)`.  The parabolic has order `p`, so its regular
permutation is a disjoint union of `p`-cycles.  The product with the natural
three-sheet mod-two action is an exact finite action of the first modular
vertex, and the preceding construction applies after doubling it.

