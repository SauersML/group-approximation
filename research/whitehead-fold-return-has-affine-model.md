---
rg: 2
id: whitehead-fold-return-has-affine-model
kind: claim
title: The occurrence-complete Whitehead fold return has a finite affine model
artifacts:
  - research/whitehead-fold-return-affine-proof.md
distinct_from:
  full-fold-compose-return-has-finite-affine-model: that gives the full two-branch compose-return table and an equivariant payload packet but does not explicitly factor and authenticate the partial Whiteheads from the same four arm actors; this proves those additional native occurrence rows inside the very same model.
  intermediate-fold-arm-has-finite-s6-model: that uses an abstract involutory conjugator for one intermediate arm and does not tie it to its coefficient-arm factors; this uses the prescribed three-factor Whitehead words for both branches, authenticates both intermediate arms and both final returns, and satisfies their adjacent braid.
  compression-preimage-whitehead-preserves-gauge: that permits an independent reservoir involution on a compressed preimage Whitehead; this realizes the Whitehead and every fold arm as one literal affine actor on a common occurrence-label packet.
---

**ESTABLISHED OCCURRENCE-COMPLETE FINITE ESCAPE.**  Retain the vector space,
fold labels, and the four literal arm actors from
`full-fold-compose-return-has-finite-affine-model`:

```text
V=<A,C,R_0,R_1>_(F_2),       C_0=C,       C_1=A+C,
[C_i,S_j]=delta_(ij)R_j,     [A,S_j]=R_j,
[T_i,R_j]=delta_(ij)A.                                  (WFR1)
```

For each branch form the prescribed partial-Whitehead word from those same
arm occurrences:

```text
W_i=S_i T_i S_i.                                       (WFR2)
```

No transported copy of an actor is introduced.  In `GL(V)` the exact rows
are

```text
S_i^2=T_i^2=W_i^2=1,
S_iT_iS_i=T_iS_iT_i,
W_iS_iW_i^(-1)=T_i,        W_iT_iW_i^(-1)=S_i,         (WFR3)
W_i(A)=R_i,                W_i(R_i)=A.                 (WFR4)
```

Moreover the two native Whiteheads satisfy

```text
W_0W_1W_0=W_1W_0W_1.                                  (WFR5)
```

Thus `(WFR2)` is the literal three-root partial-Whitehead factorization,
`(WFR3)` shares both coefficient-arm factors with the compose-return table,
and `(WFR4)` authenticates the first propagated root as the actual arm
occurrence.  The second multiplication is also occurrence-complete:
the same `T_i` in `(WFR2)` obeys

```text
[T_i,R_i]=A,              [T_i,R_(1-i)]=0,             (WFR6)
```

so the matching final output is the original marked label `A` itself, not a
new conjugate label.

All these rows hold in the finite affine group `V semidirect GL(V)`, with
`A!=0`.  They also extend to the finite equivariant `GL_5(F_2)`
payload/opposite-root packet from the preceding full-fold model: replace
each vector `v` by its character sign `D_v`, while the same `GL(V)` actors
permute the packet coordinates.  Hence the complete bounded cell has an
exact finite-dimensional unitary model with the mark at operator-norm
distance two from one.

Consequently neither literal factor sharing, authentication of both
intermediate roots, authentication of both final outputs, nor the adjacent
Whitehead braid implies `(BAC1)`.  The affine escape treats the four arms as
invertible transvections of a finite occurrence-label space rather than as
left and right multiplication on one matrix reservoir.  A successful next
row must leave this affine actor category—for example, an opposite-root
coefficient relation which simultaneously reads an arm factor **inside**
its Whitehead and its action on the same payload matrix corner, rather than
only the induced permutation of occurrence labels.

No Property `(T)`, Kazhdan input, stability theorem, trace hypothesis, or
literature result is used.

DERIVATION
whitehead-fold-return-affine-proof

