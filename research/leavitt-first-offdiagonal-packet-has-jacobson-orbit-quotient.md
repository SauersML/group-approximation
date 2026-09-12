---
rg: 2
id: leavitt-first-offdiagonal-packet-has-jacobson-orbit-quotient
kind: claim
title: The first off-diagonal packet is elementary over a partial-shift ring and has a marked Jacobson quotient
artifacts:
  - research/leavitt-first-offdiagonal-jacobson-quotient-proof.md
distinct_from:
  leavitt-first-offdiagonal-packet-breaks-locally-finite-amalgam: that extracts one infinite-order prefix substitution and fences the diagonal-core amalgam proof; this identifies the whole packet group as an elementary group over a named ring and constructs a marked quotient.
  toeplitz-finite-head-extension-preserves-root: that uses an odd-characteristic packet algebra and an additional ascending HNN endomorphism; this is the binary one-prefix orbit quotient before any compressor is adjoined.
  leavitt-cylinder-swaps-generate-thompson-in-el: that places Thompson V in a full elementary prefix group; this quotient is an elementary Jacobson group and makes no Thompson or non-LEF assertion.
---

Let `D` be the binary Cantor diagonal, put

```text
S=<D,s_0,t_0> <= L_(F_2)(1,2),
G=<EL_5(D),x_ij(s_0),x_ij(t_0)>       (i!=j),
```

and let

```text
J=F_2<S,T | TS=1>
```

be the algebraic Jacobson, or one-sided Toeplitz, algebra.  Then

```text
G=EL_5(S),                                                (JOQ1)
```

and restriction to the prefix orbit

```text
1^infinity, 01^infinity, 001^infinity, ...
```

induces a split surjection

```text
eta:G -> EL_5(J).                                        (JOQ2)
```

Writing `q=s_1t_1=1+s_0t_0`, its image in `J` is the rank-one head
projection `Q=1-ST`.  Consequently

```text
eta(x_13(q))=x_13(Q)!=1.                                 (JOQ3)
```

The Whitehead prefix shift from
`leavitt-first-offdiagonal-packet-breaks-locally-finite-amalgam` becomes a
particularly concrete permutation in this quotient.  On the basis
`(k,n)`, `1<=k<=5`, `n>=0`, it translates the bi-infinite chain

```text
...,(j,2),(j,1),(j,0),(i,0),(i,1),(i,2),...             (JOQ4)
```

by one step and fixes the other three coordinate rays.

The coefficient assignment `S->s_0`, `T->t_0` is a section of the orbit
map, so `EL_5(J)` is a marked retract of `G`.  This quotient preserves the
marked root but is not asserted here to be operator-MF.  The separate
finitely-presented-cover argument in
`leavitt-first-offdiagonal-core-is-marked-non-lef` proves that the retract
and `G` are non-LEF; the split quotient alone would not prove that fact.

DERIVATION
leavitt-first-offdiagonal-jacobson-quotient-proof
