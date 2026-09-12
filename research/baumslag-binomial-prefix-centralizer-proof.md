---
rg: 2
id: baumslag-binomial-prefix-centralizer-proof
kind: route
title: Expand a negative lamp in the c-binomial basis and move the transporter through it
target: baumslag-binomial-prefix-centralizer
requires:
  - baumslag-torsion-host-is-a-quadratic-hs-address-register
  - hs-dehn-modulus-bounded-by-dehn-function
---

On the lamp module, `b` acts by `T` and `c` by `1+T`.  Lucas' identity
expands `T^(r-1)` as the sum of `(1+T)^j` over binary submasks `j` of
`r-1`, giving `(BBC5)` with at most `r` factors.  Commute `v` through those
factors using `(BBC2)` and conjugate by `b^n`.  The expanded word has
quadratic length; the quadratic Dehn estimate and the standard normalized-HS
van Kampen telescope give `(BBC6)`.
