---
rg: 2
id: leavitt-bergman-adjoint-is-not-unit-inverse-proof
kind: route
title: Test an elementary transvection against its algebraic and transposed inverses
target: leavitt-bergman-adjoint-is-not-unit-inverse
requires: []
---

Let `A=x_12(s0)` in the twenty-leaf chart used by the degree-three and
degree-four search artifacts.  In characteristic two its algebraic group
inverse is `A` itself, and exact chart multiplication verifies `A*A=1`.
If instead `A^dagger` is obtained by replacing every support pair `(u,v)` by
`(v,u)`, exact multiplication gives

```text
A^dagger A != 1,       A A^dagger != 1.
```

The same failure occurs for `B,C,D,E,R` and for the marked commutator.  For
the latter, the correct inverse is the explicitly constructed word
`D C D C`, not the transposed support of `C D C D`.  Permutation units such
as `P`, and the order-sixteen affine packet, are the special case where the
transpose really is the inverse.

This was detected by replaying the length-twelve branch-A candidate: the
transpose convention manufactured a false one-copy hit, while algebraic
word reversal removed it.  Consequently every bounded artifact defining
generic inversion by support-pair transposition must be rerun with inverses
carried algebraically.

