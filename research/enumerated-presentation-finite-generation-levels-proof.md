---
rg: 2
id: enumerated-presentation-finite-generation-levels-proof
kind: route
title: Cofinitely killed central involutions
target: enumerated-presentation-finite-generation-levels
requires: []
---

**Upper bounds.**  `FG`: some `n` such that every generator `g_m`, `m > n`,
equals a word in `g_0, ..., g_n` in the group: `exists n forall m exists
derivation`, `Sigma^0_3`.  `FINITE`: some finite list of words contains
each generator and is closed under multiplication in the group (each
instance a `Sigma^0_1` word equality): `exists list forall generators
exists`, `Sigma^0_3`.  `T`: `FG` together with Ozawa's certificate on the
finite generating set found: `Sigma^0_3 and Sigma^0_1` inside the same
existential, `Sigma^0_3`.

**Hardness.**  `COF = {e : W_e cofinite}` is `Sigma^0_3`-complete.  Fix a
finitely presented group `K = <p, q | R>` with property (T) (`SL_3(Z)`).
Let

```text
G_e = < p, q, c_0, c_1, ... | R,  c_x^2 = 1,  [c_x, p] = [c_x, q] = [c_x, c_y] = 1,
                              c_x = 1  for x in W_e >,
```

an enumerated presentation computable from `e`.  Then
`G_e = K x (Z/2)^{(N \ W_e)}`.  If `W_e` is cofinite, `G_e = K x` (finite
elementary abelian), which is finitely generated and has (T) (a direct
product of a Kazhdan group and a finite group).  If `W_e` is coinfinite,
`G_e` maps onto `(Z/2)^{(infinite)}`, which is not finitely generated, so
`G_e` is neither finitely generated nor Kazhdan.  For `FINITE`, use
`G_e = (Z/2)^{(N \ W_e)}` (drop `K`): finite iff `W_e` cofinite.  For `FP`,
use the free product `*_{x notin W_e} Z/2` (generators `c_x` with `c_x^2 = 1`
and `c_x = 1` for `x in W_e`): finitely presentable iff finitely generated
iff `W_e` cofinite; the upper bound `exists finite generating set, exists
finite relator subset, forall relators exists derivation` is `Sigma^0_3`.
