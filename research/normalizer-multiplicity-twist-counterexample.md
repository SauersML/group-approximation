---
rg: 2
id: normalizer-multiplicity-twist-counterexample
kind: route
title: Tensor the Weil implementer with its conjugate and use the invariant Bell line
target: normalizer-multiplicity-twist-breaks-prefix-expander-rounding
requires: []
---

Write `C_q C_r=alpha(q,r)C_(qr)`.  Complex conjugation has cocycle
`conjugate(alpha(q,r))`, so the scalar factors in

```text
(C_q tensor conjugate(C_q))(C_r tensor conjugate(C_r))
```

cancel.  The semidirect covariance with `sigma(N) tensor I` follows from the
defining Clifford action, proving `(NMT1)`.

For every unitary `C`, `(C tensor conjugate(C))Omega=Omega`.  The Bell-line
projection and its associated involution therefore commute with all
normalizer checks.  If that projection lay in `I tensor End(conjugate(H))`,
its range would have dimension divisible by `dim(H)`; its rank is one and
`dim(H)>1`.  Thus it is outside the Pauli commutant.  This is an exact,
zero-defect counterexample to the missing `U tensor I` inference.

