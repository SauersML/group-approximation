---
rg: 2
id: amenable-fp-pi1-hard-from-pi2-completeness
kind: route
title: Compose the non-halting-to-totality reduction with a completeness reduction
target: amenability-of-finite-presentations-is-pi1-hard
requires: [amenability-of-finite-presentations-is-pi2-complete]
---

Map `e` to the index `f(e)` of the machine that, on input `n`, runs the `e`-th
machine on empty input for `n` steps. It diverges if that machine has halted
within `n` steps, and halts otherwise. Then `f(e) in TOT` iff the `e`-th machine
never halts.

`amenability-of-finite-presentations-is-pi2-complete` gives a computable `g` with
`g(i) in AMENABLE_fp` iff `i in TOT`. So `e -> P_e = g(f(e))` satisfies `(PI1A)`. `∎`
