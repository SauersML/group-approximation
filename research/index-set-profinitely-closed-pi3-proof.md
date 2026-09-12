---
rg: 2
id: index-set-profinitely-closed-pi3-proof
kind: route
title: Dyadic rows with a shared accumulation point
target: index-set-profinitely-closed-is-pi3-complete
requires: []
---

**Upper bound.**  `cl(W_e) = W_e` iff for every `i` either `i in W_e`
(`Sigma^0_1`) or there is `n >= 1` such that no element of `W_e` is congruent
to `i` modulo `n` (`Sigma^0_2`: an existential over `n` of the `Pi^0_1`
statement "every enumerated element avoids the class").  A universal
quantifier over a `Sigma^0_2` matrix is `Pi^0_3`.

**Infinite row.**  If `W_g(e,x)` is infinite, row `x` of (IC1) is all of
`{2^x (2j+1) : j >= 0}`.  For every `n`, taking `j = n - 1` gives
`2^x (2j + 1) = -2^x + 2^{x+1} n`, congruent to `-2^x` modulo `n`.  So
`-2^x in cl(J_e)`, and `-2^x notin J_e` since `J_e <= N`.

**All rows finite.**  Let `i in cl(J_e)`, an integer.  If `i = 0` then
`i in J_e`.  Otherwise `i` is an odd multiple of `2^x` for exactly one `x`,
i.e. `i in D_x`.  The set `D_x = 2^x + 2^{x+1} Z-hat` is clopen in
`Z-hat`, so `cl(J_e) n D_x = cl(J_e n D_x)`, and `J_e n D_x` is row `x`,
a finite set, hence closed.  Thus `i in J_e`.  So `cl(J_e) = J_e`.

**Uniformity.**  `FIN` is `Sigma^0_2`-complete uniformly, so every `Pi^0_3`
predicate `for all x, exists y, for all z, R(e,x,y,z)` has a computable
`g` with `[exists y, for all z, R] iff W_g(e,x) finite`; the enumeration of
`J_e` from `e` is computable (row `x` emits its `j`-th element when the
`(j+1)`-st element of `W_g(e,x)` appears).
