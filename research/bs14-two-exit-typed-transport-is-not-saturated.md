---
rg: 2
id: bs14-two-exit-typed-transport-is-not-saturated
kind: claim
title: The BS14 fixed-source two-exit transport is a nonsaturated three-way incidence problem
distinct_from:
  bs14-trivial-boundary-inversion-forces-r-fixed-source: that identifies the admissible source space; this computes the integer matrix after that restriction.
  bs14-residual-polar-data-build-active-dilation: that asks for an operator dilation with quantitative control; this proves that integral margins alone cannot supply its joint cells.
  iwahori-fractional-transport-integralization: that concerns two-sided block transport; the present obstruction appears because one source must serve two cubic exits simultaneously.
---

On a packet `(O,V)` in the normal form `(BP3)--(BP4)`, choose the gauge in
which all non-return maps of `R` are the identity.  Then

```text
Fix(R|H_(O,V))
  ={(xi,...,xi): xi in ker(V-1)}.                    (TET1)
```

Consequently a scalar packet contributes one admissible boundary-source
line exactly when its return phase is `v=1`, and contributes none when
`v!=1`.  For a general multiplicity packet, its number of source lines is
`dim ker(V-1)`.

After decomposing these fixed-source spaces and the two cubic exit carriers
into finite types, an exact joint cell has three labels

```text
(i,j,k) in I_source x J_exit,1 x K_exit,2.            (TET2)
```

If `E` is the set of cells allowed by the packet phase and Gram equations,
their integer multiplicities `n_(ijk)` have margins

```text
sum_(j,k) n_(ijk)=s_i,
sum_(i,k) n_(ijk)=e^(1)_j,
sum_(i,j) n_(ijk)=e^(2)_k.                            (TET3)
```

Thus the necessary integer matrix is the vertex--hyperedge incidence
matrix `A_E` of a three-partite three-uniform hypergraph: every column has
one `1` in each of the three row families.  This is not, in general, a
network matrix and is not totally unimodular.

Indeed take two labels in each family and allow only the four even-parity
cells

```text
111, 122, 212, 221.                                  (TET4)
```

The submatrix on rows `s_1,e^(1)_1,e^(2)_1,s_2` is

```text
M=[1 1 0 0]
  [1 0 1 0]
  [1 0 0 1]
  [0 0 1 1],                  det(M)=2.              (TET5)
```

Moreover, prescribing every one of the six margins in `(TET3)` to equal
one has the unique nonnegative real solution

```text
n_111=n_122=n_212=n_221=1/2,                          (TET6)
```

and no integer solution.  Doubling all six margins admits the integer
solution with all four cell multiplicities equal to one.  Hence the typed
cell semigroup can have an index-two hole even though every marginal is an
integer and all three families have the same total size.

This is a necessary combinatorial fence, not a BS14 counterexample by
itself: one must still show that the native packet/Gram support `E` contains
such a parity cycle.  Conversely, a positive proof cannot cite ordinary
transportation-polytope integrality.  It must prove that the **native**
support hypergraph is balanced/saturated, pay and pad its parity holes, or
use the operator Gram equations to rule those holes out.  The involution
equations `(TBI3)` impose further positive-semidefinite compatibility, so
integer solvability of `(TET3)` is necessary and not sufficient.

