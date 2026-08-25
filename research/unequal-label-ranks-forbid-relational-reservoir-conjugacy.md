---
rg: 2
id: unequal-label-ranks-forbid-relational-reservoir-conjugacy
kind: claim
title: Exact tensor-factor relations cannot conjugate reservoir gauges carried by unequal label involutions
distinct_from:
  literal-fiber-unequal-reflection-row-collapses-packet: that uses the canonical group trace to rule out a literal group word conjugating unequal coarse and fine projections; this is a representation-theoretic no-go for cancelling a finite exact label packet in order to deduce conjugacy of its spectator gauges.
  adjacent-prefix-whitehead-braid-conjugates-reservoir-gauges: that positively applies a Coxeter braid when the two label swaps have the same one-quarter negative rank; this proves why the same exact relational mechanism cannot be repaired by replacing one label swap with the required one-eighth involution.
  three-gauge-tests-leave-a-tensor-spectator: that inserts an invisible tensor factor into a particular finite test family; this treats every exact group-relational tensor cancellation whose conclusion is reservoir conjugacy.
---

Let

```text
P=<x_1,...,x_n | R>
```

be any group presentation.  Suppose `A_i in U(L)` is an exact
`P`-representation, take arbitrary `V_i in U(M)`, and put

```text
W_i=A_i tensor V_i.
```

Assume that the tuple `W` is also an exact `P`-representation.

Every group word separates exactly:

```text
r(W)=r(A) tensor r(V).                                  (URC1)
```

Since `r(A)=I` and `r(W)=I` for every defining relator, `(URC1)` gives
`r(V)=I`; hence `V` is itself a `P`-representation.  Consequently every
equality between group words that is deduced solely from `R` holds in the
label tuple and in the reservoir tuple separately.  In
particular, if the proposed packet relations imply

```text
x_j=q x_i q^(-1) in P,                                  (URC2)
```

then necessarily

```text
A_j=q(A)A_iq(A)^*,       V_j=q(V)V_iq(V)^*.             (URC3)
```

Thus an exact tensor-factor cancellation cannot force the reservoir gauges
`V_i,V_j` to be conjugate unless the fixed label operators `A_i,A_j` are
conjugate as well.

For self-adjoint involutions, conjugacy preserves the normalized dimension of
the negative spectral projection.  Hence no such exact relational packet can
both

```text
negative_fraction(A_i)=1/4,
negative_fraction(A_j)=1/8                              (URC4)
```

and deduce conjugacy of `V_i,V_j` by cancelling the label tensor factor.

Applied to the adjacent prefix Whitehead packet, the Coxeter braid succeeds
precisely because `SWAP_(1,2)` and `SWAP_(2,3)` are conjugate label
involutions, each with negative fraction `1/4`.  Replacing the second swap by
a controlled single-pair transposition of negative fraction `1/8` destroys
the possibility of any exact group-consequence proof of reservoir conjugacy
using the same separated label/reservoir representation.  A viable native
two-scale proof must therefore use a nonseparated occurrence row, a
matrix-dependent polar overlap, or another mechanism that does not amount to
an exact relation in a tensor product of two independent `P`-models.
