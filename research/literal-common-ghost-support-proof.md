---
rg: 2
id: literal-common-ghost-support-proof
kind: route
title: Compare the nonzero group-basis supports of the two Fourier idempotents
target: literal-common-ghost-atom-classicalizes-contexts
requires: []
---

The elements of `Gamma` form a linearly independent basis of `C[Gamma]`.
Every coefficient in `(LCG1)` is nonzero, so the group-basis support of
`e_(H_i,chi_i)` is exactly `H_i`.  Equality `(LCG2)` therefore first gives
`H_1=H_2`.  Equality of the coefficient of each `h` then gives
`chi_1(h)/|H_1|=chi_2(h)/|H_2|`, and hence `chi_1=chi_2`.

For elementary abelian context groups, every assignment projection has the
form `(LCG1)`.  Equality of complements is equivalent to equality of the
atoms.  Once the two subgroup images coincide, every generator of either
context belongs to the same abelian subgroup, proving the classicalization
statement.

