---
rg: 2
id: trace-conditioned-reverse-kleene-proof
kind: route
title: Add canonical moments to the reverse proof-enumeration diagonal
target: trace-conditioned-reverse-kleene-collapse
requires:
  - word-problem-of-finite-presentation-is-re
---

Given `e`, compute `(Gamma_e,w_e)` and let `N_e` enumerate the finite van
Kampen consequences of `R_e`, halting exactly when it finds a proof of
`w_e=1`.  Kleene's recursion theorem supplies `e_*` whose machine has the
same behavior as `N_(e_*)`.

If `e_*` halted, the enumerated proof would give `w_(e_*)=1`, whereas `(TCR2)`
would give `w_(e_*)!=1`.  Hence `e_*` does not halt.  Completeness of the
enumeration also gives

```text
w_(e_*) != 1 in Gamma_(e_*).                             (TCR6)
```

Suppose `Gamma_(e_*)` were hyperlinear.  Canonical-trace microstates have
relator defect tending to zero and converge on every fixed word moment.
By `(TCR3)`, they therefore eventually satisfy every strict inequality in
`(TCR4)`.  By `(TCR6)`, their marked distances satisfy

```text
||w_(e_*)(U_n)-I||_2^2 -> 2.
```

For all sufficiently large `n` this is strictly larger than
`alpha_(e_*)`, contradicting `(TCR5)`.  Thus `Gamma_(e_*)` is
nonhyperlinear.  Notice that the fixed-point machine never searches for a
matrix tuple, so adding the moment side conditions changes neither its code
nor the halting contradiction.
