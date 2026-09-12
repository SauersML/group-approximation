---
rg: 2
id: every-forbidden-atom-has-fixed-schur-pauli-words-proof
kind: route
title: Clear the Schur row and column at one fixed selector assignment
target: every-forbidden-atom-has-fixed-schur-pauli-words
requires:
  - boolean-predicate-is-one-rank-jump
  - predicate-rank-gate-doubles-restriction-multiplicity
artifacts:
  - experiments/fanizza_fixed_predicate_rank_compiler.py
---

Put `A=U(a)`.  Right multiplication of `(SPW1)` by

```text
C=[[I,A^-1 v],[0,1]]
```

clears the top-right block.  Left multiplication by

```text
R=[[I,0],[w^T A^-1,1]]
```

then clears the bottom-left block.  Since the Schur complement is one,

```text
R M(a) C=diag(A,1).                                    (1)
```

Row operations replace commuting p-generators by their products and column
operations do the same to the commuting q-generators.  The last transformed
row and column are exactly the words `(SPW3)`.  Equation `(1)` says that they
pair trivially with every baseline generator and pair nontrivially with one
another, proving `(SPW4)`.

All coefficients in `(SPW2)` are constants after the atom `a` is fixed.
The accompanying exact audit solves both binary systems for every forbidden
atom of the three Fanizza predicates and verifies the clearing equations and
unit Schur complement.
