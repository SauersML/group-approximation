---
rg: 2
id: amenable-fp-not-re-from-pi1-hardness
kind: route
title: A recursively enumerable amenable locus would make non-halting recursively enumerable
target: amenable-finite-presentations-are-not-recursively-enumerable
requires: [amenability-of-finite-presentations-is-pi1-hard]
---

Let `e -> P_e` satisfy `(PI1A)` of `amenability-of-finite-presentations-is-pi1-hard`.
If `AMENABLE_fp` were enumerated by some algorithm, then
`{ e : P_e in AMENABLE_fp }` would be recursively enumerable, as the preimage of
a c.e. set under a total computable map. By `(PI1A)` that set is the non-halting
set, whose complement is also c.e. So the halting problem would be decidable, a
contradiction. `∎`
