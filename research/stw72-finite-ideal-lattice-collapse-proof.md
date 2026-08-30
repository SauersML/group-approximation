---
rg: 2
id: stw72-finite-ideal-lattice-collapse-proof
kind: route
title: Filter a finite ideal lattice by simple weakly purely infinite subquotients
target: stw72-finite-ideal-lattice-wpi-is-purely-infinite
requires:
  - stw72-chain-ideal-wpi-is-purely-infinite
---

Choose a maximal chain in the finite ideal lattice,

```text
0=I_0 proper subset I_1 proper subset ... proper subset I_m=A.
```

Each subquotient `I_j/I_(j-1)` is simple.  Indeed, every closed two-sided
ideal of an ideal of a C-star algebra is again an ideal of the ambient
algebra.  Thus a nontrivial ideal in `I_j/I_(j-1)` would lift to an ideal
strictly between two consecutive members of the maximal chain.

Weak pure infiniteness passes both to closed ideals and to quotients.  The
ideal assertion is also immediate from the Cuntz-semigroup formulation: the
canonical copy of `Cu(I)` is an order ideal of `Cu(A)`, so the identity

```text
n x = infinity x
```

for `x in Cu(A)` restricts to `Cu(I)`.  The quotient assertion is the usual
quotient permanence of weak pure infiniteness.  Consequently every
`I_j/I_(j-1)` is weakly purely infinite.

The closed ideal lattice of a simple algebra is linearly ordered, so
`stw72-chain-ideal-wpi-is-purely-infinite` makes each nonzero subquotient
`I_j/I_(j-1)` purely infinite.  Finally, Kirchberg--Rordam pure infiniteness
is preserved under extensions.  Starting with `I_0=0` and applying that
extension theorem successively to

```text
0 -> I_(j-1) -> I_j -> I_j/I_(j-1) -> 0
```

shows inductively that every `I_j`, and hence `A`, is purely infinite.

The two finiteness uses are sharp features of this proof rather than hidden
regularity assumptions: finiteness supplies a composition chain, while
extension permanence glues across incomparable ideals without attempting to
fuse their square-zero witnesses inside one hereditary subalgebra.

