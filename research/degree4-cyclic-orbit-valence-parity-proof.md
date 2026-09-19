---
rg: 2
id: degree4-cyclic-orbit-valence-parity-proof
kind: route
title: Count fundamental-domain boundary crossings in all four lifts
target: degree4-cyclic-orbit-valence-parity
requires:
  - degree-kernel-abelianization-is-infinite-cyclic
---

Lift the exponent path simultaneously from the four residues modulo four.
For each unit step of the original path, exactly one of these four translated
steps crosses a boundary between consecutive fundamental domains.  In the
cyclic Reidemeister--Schreier rewrites these crossings are exactly the signed
`z=t^4` occurrences.  Summing absolute occurrences over the four lifts
therefore counts every one of the `n` unit steps once, proving
`sum_i v_i=n`.

Each lifted relator represents total stable-letter exponent four.  After
writing it in the kernel generators, its signed `z` exponent is consequently
one.  Hence the number of positive occurrences minus the number of negative
occurrences is one in every orbit, and each absolute valence `v_i` is odd.
Substitution of `(1,1,v,v)` into the sum gives `n=2v+2`.
