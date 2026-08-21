---
rg: 2
id: sl3-collapse-via-carrier-character-rigidity
kind: route
title: The compression turns the collapse into carrier character rigidity, which the factorial claim supplies
target: sl3-pair-relative-commutant-route
requires:
  - rcc-carrier-character-face-compression
  - hnn-carrier-factorial-character-collapse
---

Instantiate `rcc-carrier-character-face-compression` at
`(Gamma, Lambda) = (SL_3(Z[1/2]), SL_3(Z))`.  The hypotheses hold:
`Z(Gamma)` is trivial (a scalar `zeta I in SL_3` needs `zeta^3 = 1`
with `zeta in Z[1/2]`, so `zeta = 1`), `Gamma` is ICC (a nontrivial
element has finite `Lambda`-centralizer by the relative-icc computation
recorded in `relative-commutant-collapse-for-sl2-pair`, hence infinite
conjugacy class), `Lambda` is proper, and `Gamma` is finitely
generated linear, hence residually finite (Malcev) and hyperlinear.

The compression then says: the collapse `(RC3)` -- the statement of
`sl3-pair-relative-commutant-route` -- holds if and only if every
factorial hyperlinear character of the carrier
`H = < Gamma, t | [t, Lambda] = 1 >` restricting to `delta_e` on
`Gamma` centralizes `t`.  That is precisely
`hnn-carrier-factorial-character-collapse` at `n = 3`, `p = 2`.
Combining the two gives `(RC3)`.

What the route changes strategically: the remaining open input
mentions no ultraproduct, no representation variety and no stability
-- it is a character-rigidity statement about one countable group, the
formulation in which the higher-rank rigidity literature
(Peterson, Bekka--Boutonnet--Houdayer) actually operates, so progress
there transfers with no translation layer.
