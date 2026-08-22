---
rg: 2
id: finite-quotient-graph-product-amplification-proof
kind: route
title: Separate a missing edge in a finite actor quotient and amplify its regular representation
target: finite-graph-product-amplifications-block-hs-collapse
requires: []
---

Choose a finite quotient

```text
q:A -> Q
```

such that `q(r)` is distinct from `1` and from every element of
`q(D union D^(-1))`.  Residual finiteness supplies one quotient: intersect
finite-index normal subgroups separating the finitely many nonidentity
elements

```text
r,  r d^(-1)  (d in D union D^(-1)).                  (FQP1)
```

Let `bar D=q(D union D^(-1))`, discard the identity from `bar D`, and form
the finite graph `Graph_barD(Q)`.  Identifying the vertex `a` with `q(a)`
respects every edge of `Graph_D(A)`.  Hence the graph-product universal
property gives an `A`-equivariant homomorphism

```text
K_D -> K_barD(Q),  c_a |-> c_(q(a)),                  (FQP2)
```

where the actor action on the target factors through `Q`.  Consequently
`(FQP2)` extends to

```text
G_D -> K_barD(Q) rtimes Q.                             (FQP3)
```

By the choice of `q`, the vertices `1` and `q(r)` are distinct and
nonadjacent.  The graph-product normal form therefore gives

```text
[c_1,c_(q(r))] != 1.                                  (FQP4)
```

The graph in `(FQP3)` is finite.  A finite graph product of finite groups is
residually finite.  Its semidirect product by the finite group `Q` is also
residually finite: if a kernel element `k` is separated by a finite-index
normal subgroup `N`, replace `N` by the finite intersection of its
`Q`-conjugates.  This is `Q`-invariant, still finite index, and still excludes
`k`.  Thus `(FQP4)` survives in a finite quotient `F` of `(FQP3)`.

Let `lambda_F` be the left regular representation of `F`.  A nonidentity
group element has normalized trace zero in this representation, and hence

```text
||lambda_F([c_1,c_(q(r))])-I||_2^2
 =2-2 Re tau_F(lambda_F([c_1,c_(q(r))]))
 =2.                                                   (FQP5)
```

Pulling back along `(FQP3)` proves `(FQA2)` in one finite dimension.  Taking
the direct sum of `n` copies gives dimensions tending to infinity without
changing any normalized-HS defect or the value `sqrt(2)` in `(FQP5)`.

If `A` has property `(T)` and `D` contains a Kazhdan set, the graphs
`Graph_barD(Q)` have a uniform spectral gap as `Q` varies.  Equations
`(FQP3)--(FQP5)` are nevertheless exact on every member of that family.
Therefore a Poincare or one-dimensional cosystolic estimate for the checked
edge graph cannot imply a missing commutator estimate.  Such an estimate
controls gradients of a common vector-valued field; the independent vertex
involutions of a graph product are not forced to arise from such a field.
