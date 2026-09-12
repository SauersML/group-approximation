---
rg: 2
id: schur-clock-router-has-maximal-projective-leak
kind: claim
title: A cyclic Schur router admits an exactly central clock with maximal projective target leakage
distinct_from:
  sl3-hnn-fold-determinant-and-index-are-trace-blind: that realizes a trace-zero commutator for two otherwise unconstrained matrices; this keeps an arbitrary block-diagonal source representation and every prescribed block transport while placing the clock in the exact source commutant.
  folner-multiplicity-atlases-have-vanishing-first-exit: that constructs coherent partial isotypic transports with small boundary but does not produce the auxiliary central unitary or calculate its projective target energy; this supplies the exact multiplicity-clock calculation.
  arith-clifford-covariance-preserves-projective-energy: that tensors an already existing enemy through projective normalizer data; this constructs the projective leak intrinsically from a cyclic Schur router.
---

Let

```text
H=direct_sum_(j in Z/NZ) H_j,       dim H_j=m,
```

and let `D` be any unital algebra preserving every `H_j`.  Suppose a
unitary router `V` sends `H_j` onto `H_(j+1)`.  Then there is a unitary
`U in D'` such that

```text
tr_H([U,V])=0,
1-|tr_H([U,V])|^2=1.                                  (SCR1)
```

More precisely, if `zeta` is a primitive `N`th root and
`alpha^N=(-1)^(N-1)`, choose scalars `q_j` cyclically so that

```text
q_j conjugate(q_(j-1))=alpha zeta^j.                   (SCR2)
```

The compatibility condition is exactly
`product_j alpha zeta^j=1`, so such `q_j in T` exist.  Put

```text
U|_(H_j)=q_j I.                                        (SCR3)
```

Then `U` commutes with the WHOLE block-diagonal algebra `D`, whereas
`[U,V]` is block diagonal with scalar `alpha zeta^j` on `H_j`.  Its
normalized trace is zero, proving `(SCR1)`.

This remains true when each block carries arbitrary finite-congruence,
Clifford, or Weil data and each arrow is a prescribed unitary intertwiner:
the calculation uses only the block permutation.  Changing an arrow by a
scalar Mackey gauge also leaves `(SCR1)` unchanged.  Hence the following
data, even taken together, cannot prove projective trace-square transfer:

```text
* all source characters and conductor labels on the blocks;
* all dimensions and Schur multiplicities;
* existence and ranks of the transition intertwiners;
* scalar Weil/Mackey cocycles on the arrows.             (SCR4)
```

Indeed these data are identical before and after adjoining the clock
`(SCR3)`, while the source projective energy of `U` is exactly zero and its
target energy at the router is maximal.

For the `SL_3` projective-transfer problem this is a firewall, not a full
countermodel.  Co-density forbids such a cycle in an exact finite
representation of `SL_3(Z[1/p])`; an approximate arithmetic enemy must
manufacture it by closing a long conductor path across a small boundary.
The claim says precisely what a character/Weil/congruence proof must add:
it must either prove a NON-FOLNER bound for the authenticated transport
graph, or constrain the literal composition of the arrows on one common
multiplicity reservoir.  Classification of the vertices and scalar
projective holonomy of the arrows is insufficient.

