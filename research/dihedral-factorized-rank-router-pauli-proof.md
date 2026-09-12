---
rg: 2
id: dihedral-factorized-rank-router-pauli-proof
kind: route
title: Solve the D8 lift equations and insert a balanced transverse multiplicity Pauli
target: dihedral-factorized-rank-router-has-pauli-overlap-model
requires: []
artifacts:
  - research/artifacts/hybrid-rank-router-tensor-closure-2026-08-23.md
---

On the negative D8 spin sector write `z=diag(I,-I)` and use `j` to identify
the two equal halves.  If `r=diag(R_+,R_-)`, then `(rj)^2=a` gives

```text
R_+R_-=R_-R_+=A.
```

Putting `W=R_-` gives `R_+=AW`; the involution laws make `W` commute with
`A`.  The same calculation gives `s=diag(BV,V)`.  The three cross
commutators in `(DFR1)` make `A,B,W,V` commute, so direct multiplication
gives `(DFR3)`.

Substitute `(DFR4)`.  Then `G=Z`, `R=-I tensor Z`, and `S=I tensor Z`.
Conjugation by `I tensor X` flips `Z`, proving `(DFR5)`.  This is a finite
exact matrix representation with negative central mark and maximal
forbidden overlap, so no robust overlap bound follows from the displayed D8
assembler relators.
