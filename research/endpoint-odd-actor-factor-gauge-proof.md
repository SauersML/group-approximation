---
rg: 2
id: endpoint-odd-actor-factor-gauge-proof
kind: route
title: Apply the simultaneous central involution to the two native factors
target: endpoint-odd-actor-retains-native-factor-gauge
requires:
  - endpoint-order-five-actor-has-half-gram
  - full-packet-cyclic-aggregates-retain-positive-endpoint-gram
  - native-whitehead-hecke-head-has-order-seven-anchor
---

Write `v_2=B_3A_2`, so the literal words occurring in the endpoint actor are

```text
M=J_2v_2,                    C=WM.                    (1)
```

Let `D` be a central involution on a multiplicity coordinate.  Centrality
and `D^2=1` give

```text
(J_2D)(v_2D)=J_2v_2D^2=M.                             (2)
```

Consequently `M^7`, `(WM)^5`, the conjugation representation on `V`, the
returning `GL_3(F_2)` subgroup, and every expression in `W,M` are literally
unchanged.  The projections `p_2,p_*` are defined by the signed sheet and
the endpoint word `W`, not by a chosen factorization of `M`.  The orbit joins
`E_M,E_C` are joins of translates by the unchanged products.  Hence all
positive Gram and polar conclusions of the two required claims are
unchanged as well.

On the other hand the mixed Hecke factor is `u_2=v_2A_1`.  If `A_1` is kept
fixed, the second change in `(2)` gives

```text
u_2 -> (v_2D)A_1=u_2D.                                (3)
```

The order-seven identity does not see `(3)`, because its gauged product is
still exactly `M` by `(2)`.  This is different from inserting `D` in only
one factor, where `(OWH5)` returns `D` after the seventh power.

Finally take a nonzero multiplicity block and `D=-I`.  The two values of the
right side of `(3)` differ by

```text
||u_2-(-u_2)||=2.                                     (4)
```

Every nonzero subprojection reducing this scalar `D` retains the same
distance.  Thus no algebraic construction which uses only the unchanged
endpoint actor, its spectral cuts, and its cyclic joins can select one of
the two exposed `u_2` factors.  This proves the scoped claim.

The argument concerns the stated factor-occurrence interface.  It is not a
representation of the entire elementary group with one root arbitrarily
sign-twisted, and therefore it is not a countermodel to a future ordinary
Steinberg relation that meets one factor with odd parity.
