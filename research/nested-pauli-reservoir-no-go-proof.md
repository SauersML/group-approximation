---
rg: 2
id: nested-pauli-reservoir-no-go-proof
kind: route
title: Exhibit the coherent nested Pauli rectangular model
target: gowers-hatami-uniqueness-does-not-lock-nested-pauli-reservoirs
requires: []
---

On `H_N=(C^2)^(tensor N)`, represent `E_n` on the first `n` qubits:

```text
rho_n=pi_n tensor I_(2^(N-n)).
```

All inclusions are exact, while multiplicities satisfy
`m_n=2m_(n+1)`.  Thus the label degree doubles and multiplicity halves at
constant ambient dimension and zero defect.

The commutant of `rho_n(E_n)` is the full remaining matrix algebra.  Any
unitary in it may conjugate the proposed next Pauli pair, producing another
exact `E_(n+1)` extension with exactly the same restriction to `E_n`.
Therefore the input distance for fixed-level uniqueness is zero even though
the child `M_2` subfactor is arbitrary.  Exactifying the largest fixed table
once makes all lower levels coherent, but leaves this same rectangular
model.  Only a relation comparing two extension routes can force the
relative gauge into the smaller child commutant.
