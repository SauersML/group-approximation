---
rg: 2
id: expander-parity-checks-dense-clifford-shear-proof
kind: route
title: Conjugate the named X chart by a quarter-turn about a codeword Z string
target: expander-parity-checks-have-dense-clifford-shears
requires: []
---

For `v in ker(H)`, the Pauli word `P=Z(v)` commutes with every `Z(b)` and
with every `X(h)` for `h in rowspan(H)`.  Therefore its quarter-turn
`W=exp(pi i P/4)` fixes those observables pointwise.  Simultaneous
conjugation by `W` preserves all Weyl relations.  At coordinate `i`, it fixes
`X_i` if `v_i=0`; if `v_i=1`, anticommutation gives
`W X_i W*=iPX_i`.  Distinct nontrivial Pauli words are orthogonal for the
normalized matrix trace, hence the latter is at squared `2`-distance `2`
from `X_i`.  Summing over coordinates outside an arbitrary bad set proves
`(EPCS4)`.  The positive-distance conclusion follows from
`|supp(v)|>=Delta n`.

