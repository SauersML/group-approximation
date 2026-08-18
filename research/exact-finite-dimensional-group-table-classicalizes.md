---
rg: 2
id: exact-finite-dimensional-group-table-classicalizes
kind: claim
title: Every exact finite-dimensional separated group table has an exact finite permutation model
---

Let `T` be a finite partial multiplication table on a finite label set `F`.
Suppose matrices `U_x in U(d)` are assigned to `x in F` so that every listed
product `xy=z` satisfies `U_x U_y = U_z` exactly and distinct labels are
represented by distinct matrices (in particular this holds on the exact
regular-character face, where `tau(U_x^* U_y)=0` for `x != y`).  Then there is
a finite set `X` and permutations `sigma_x in Sym(X)` satisfying every listed
product exactly and with `sigma_x` and `sigma_y` disagreeing at every point
for `x != y`.

Consequently an exact finite-dimensional quantum solution cannot witness a
quantum/classical gap for a group table.  Any witness to
`finite-table-quantum-classical-hamming-gap` must have defect tending to zero
only along unbounded matrix dimensions; the zero quantum infimum cannot be
attained in one finite dimension.
