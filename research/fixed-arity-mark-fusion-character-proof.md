---
rg: 2
id: fixed-arity-mark-fusion-character-proof
kind: route
title: Realize all fused marks as nonzero characters of one binary vector space
target: fixed-arity-mark-fusion-has-finite-character-model
requires: []
---

Multiplication of the diagonal operators in `(FMF3)` is addition of their
labels, proving `(FMF4)`.  A nonzero linear functional on `F_2^r` has a
kernel of size `2^(r-1)`, so its sign has equal positive and negative ranks.

For nonzero `a,b in F_2^r`, extend each to a basis and send the first basis
to the second.  This gives an invertible binary linear map `A` carrying `a`
to `b`.  Use its contragredient permutation
`delta_x |-> delta_(A^(-T)x)` of `F_2^r`; direct substitution conjugates
`D_a` to `D_(Aa)=D_b`, proving `(FMF5)` without a transitivity theorem.  The controlled-Pauli extension is
then literal tensor conjugation.  All matrices lie in the displayed finite
semidirect product, completing the construction.
