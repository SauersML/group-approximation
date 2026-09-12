---
rg: 2
id: positive-one3-global-clock-dualization-proof
kind: route
title: Count qutrit exponents in each positive ONE3 clause
target: positive-one3-global-clock-is-z3-lcs-plus-unary-sector
requires: []
---

If `P_x,P_y,P_z` are orthogonal and sum to one, the unitaries `(GQ1)`
commute.  On the range of `P_x` their eigenvalues are `(1,omega,omega)`,
and cyclically on the other two ranges.  Their product is therefore
`omega^2` everywhere, proving `(GQ2)`; `(GQ3)` is immediate from `(GQ1)`.

Conversely, `(GQ3)` gives a joint spectral decomposition of every commuting
clause into exponent profiles

```text
(e_x,e_y,e_z) in {0,1}^3,
U_i=omega^(e_i).
```

Equation `(GQ2)` says `e_x+e_y+e_z=2 mod 3`.  An integer between zero and
three which is congruent to two modulo three is exactly two.  Hence every
nonzero joint spectral atom has exactly two exponents equal to one and one
exponent equal to zero.  The projections `P_i=Pi_1(U_i)` are therefore
pairwise orthogonal and sum to one.  Since `U_v` is indexed globally, two
occurrences of the same Boolean variable decode the same projection.
