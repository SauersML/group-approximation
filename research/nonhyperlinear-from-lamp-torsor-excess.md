---
rg: 2
id: nonhyperlinear-from-lamp-torsor-excess
kind: route
title: Excess lamp-torsor entropy against the Cartan ceiling makes the summit wreath non-hyperlinear
target: non-hyperlinear-group
requires:
  - coset-wreath-hyperlinearity-forces-strong-one-boundedness
  - coset-wreath-microstates-carry-excess-entropy
---

Suppose both prerequisites.  If `W_3` were hyperlinear, the excess
claim gives `h(L(W_3)) > 0` while the Cartan-ceiling theorem gives
`h(L(W_3)) <= 0` — contradiction.  So `W_3 = (direct_sum_{Gamma/Lambda}
C_2) rtimes SL_3(Z[1/3])`, a finitely generated explicit group (the
base lamp and generators of `SL_3(Z[1/3])`), is not hyperlinear, which
is the goal witness.

This is the first route into the goal whose open content is a
microstate-COUNTING lower bound rather than a commutant exclusion, a
stability hypothesis, or a compiler: the enemy is defeated by having
too many shapes rather than none.  The mechanism is Voiculescu's
absence-of-Cartan argument run backwards — the lamp masa is a genuine
Cartan in `L(W_3)` (`coset-wreath-algebra-has-a-lamp-cartan`), so
hyperlinearity starves the model space; any macroscopic moduli in a
model construction overfeed it.

Relation to the neighbouring routes: it shares its target group with
`nonhyperlinear-coset-wreath-from-p3-collapse` but consumes no collapse,
no correctability, and no outlier exclusion; conversely, if the
Lambda-exact constructive probes ever exhibit an enemy WITH surviving
`c d^2`-scale non-conjugate freedom, this route closes the goal even
though the collapse route would simultaneously die.  The two routes
cover the fork's two halves.
