---
rg: 2
id: shift-raag-family-lef-sofic-proof
kind: route
title: Periodic truncation of the shift graph for LEF, sofic-by-amenable for soficity
target: shift-raag-family-is-always-lef-and-sofic
requires:
  - shift-raag-family-classifies-amenability
---

Soficity: `A(Gamma_J)` is a right-angled Artin group on a countable graph,
residually finite (its finitely generated subgroups lie in finitely
generated parabolic retracts) hence sofic, and `G_J` is its extension by
`Z`, sofic by Elek--Szabo.

LEF: a word of length `<= 2r` in `a^{+-1}, t^{+-1}` rewrites as `u t^k`
with `|k| <= 2r` and `u` a word in `a_i`, `|i| <= 2r`; triviality depends
only on the full subgraph `W` of `Gamma_J` on that window, i.e. on
`J n [1, 4r]`.  Put `J_r = J n [1, 4r]`, choose `m > 8r + 1`, and let
`Gamma'` be the graph on `Z/m` with `u -- v` iff `v - u in +-J_r mod m`;
its window on `{|i| <= 2r}` is isomorphic to `W`, and the shift is an
automorphism.  `H' = A(Gamma') x| Z/m` is residually finite, and
evaluating ball words (`a |-> a_0`, `t |-> ` the generator) is well
defined, injective and multiplicative on the ball of radius `r` exactly as
in [[centralizing-hnn-always-lef-proof]]; a finite quotient of `H'`
separating the finite image completes the local embedding.
