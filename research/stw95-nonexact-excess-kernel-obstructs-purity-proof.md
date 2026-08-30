---
rg: 2
id: stw95-nonexact-excess-kernel-obstructs-purity-proof
kind: route
title: View the tensor-exactness defect as an ideal-subquotient of the product
target: stw95-nonexact-excess-kernel-obstructs-purity
requires: []
---

Minimal tensoring preserves the injection `I->A`, so
`I tensor_min B` is an ideal contained in `K`.  Thus `K` is an ideal of
`A tensor_min B` and `E` is a quotient of that ideal.  By
Perera--Thiel--Vilalta's extension theorem, purity passes from an algebra to
every ideal and quotient.  If `A tensor_min B` were pure, then `K` and then
`E` would be pure, contrary to hypothesis.

Exactness of `B` is precisely the assertion that for every such extension
`K=I tensor_min B`; in that case the excess quotient is zero.  The criterion
does not assert that a nonpure excess quotient exists for pure factors.
