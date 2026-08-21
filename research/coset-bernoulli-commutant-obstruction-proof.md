---
rg: 2
id: coset-bernoulli-commutant-obstruction-proof
kind: route
title: The distinguished coset coordinate is central for C and moved by A
target: coset-bernoulli-ce-refutes-relative-commutant-collapse
requires: []
---

In the generalized Bernoulli action `A curvearrowright K^(A/C)`, the base
coset `C` is fixed pointwise by `C`.  Hence every bounded function of that
coordinate commutes with the canonical unitaries `u_c`.  Choose a nonconstant
circle-valued coordinate function `v`.  If `a notin C`, then `aC != C`, and
`u_a v u_a^*` is the same function on the distinct coordinate `aC`; the two
functions are unequal in `L^infinity(K^(A/C))`.  Therefore `v` commutes with
`pi(C)` but not with `pi(a)`.

The canonical group-measure-space trace satisfies `tau(u_a)=0` for every
`a!=1`, so the group copy has its regular trace.  Any trace-preserving
embedding of the crossed product into a tracial matrix ultraproduct preserves
the two commutation statements.  This proves `(CB5)` and its contrapositive.
