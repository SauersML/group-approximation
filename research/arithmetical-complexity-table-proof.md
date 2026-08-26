---
rg: 2
id: arithmetical-complexity-table-proof
kind: route
title: Each cell is one of the cited claims; the folklore cells are the standard index-set facts
target: arithmetical-complexity-table-of-group-properties
requires:
  - second-level-rice-theorem-for-local-approximation-properties
  - sofic-recognition-two-generator-recursive-is-pi2-complete
  - sofic-recognition-finite-presentations-arithmetical-position
  - approximation-property-recognition-dichotomy
  - amenability-two-generator-recursive-is-pi2-complete
  - amenability-of-finite-presentations-arithmetical-position
  - residual-finiteness-two-generator-recursive-is-pi3-complete
  - residual-finiteness-of-enumerated-presentations-is-pi3-complete
  - residually-p-two-generator-recursive-is-pi3-complete
  - kazhdan-property-t-of-finite-presentations-is-sigma1-complete
  - mf-recognition-two-generator-recursive-is-pi2-complete
---

The cited claims supply every non-folklore cell.  The folklore cells:
triviality of a finite presentation is `Sigma^0_1` (Todd--Coxeter, or
enumerate derivations of `x = 1` for each generator) and `Sigma^0_1`-hard
by the Rabin collapse (`K(w) = 1 iff w = 1`); triviality of an enumerated
presentation is "every generator is trivial", a universal quantifier over
`Sigma^0_1` events, and `Pi^0_2`-hard by the parametric switch with any
nontrivial finite seed.  The `contains F_2` cell on finite presentations:
`Sigma^0_2` upper bound as in the two-generator case; the Rabin group
contains `F_2` iff `w != 1`, giving `Pi^0_1`-hardness.  Metabelian on
finite presentations is `Pi^0_2` for the same reason as on recursive ones,
and `Sigma^0_1`-hard (the Rabin group is trivial iff `w = 1` and contains
`F_2` otherwise); completeness is open with the amenable cell.
