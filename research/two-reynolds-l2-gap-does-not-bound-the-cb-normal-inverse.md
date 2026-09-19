---
rg: 2
id: two-reynolds-l2-gap-does-not-bound-the-cb-normal-inverse
kind: claim
title: Two order-three Reynolds expectations can have a uniform L2 gap and logarithmically divergent cb normal inverse
distinct_from:
  exact-passive-jacobian-is-two-reynolds-expectations: that reduces the arithmetic passive Jacobian to a constrained Reynolds column; this proves an unconditional no-go for deducing its cb bound from finite dimensionality and an L2 angle alone.
  relative-tangent-spectral-cuts-can-have-full-bs-hull: that refutes an L2 spectral-cut repair inside one BS packet; this is a scalar gauge-normal Green-operator obstruction for pairs of order-three Reynolds expectations.
  constrained-reynolds-column-has-a-diagonal-scalar-shadow: that extracts the special arithmetic signed-incidence family; this counterexample concerns general Reynolds columns and does not by itself refute that special family.
---

**ESTABLISHED; GENERIC REYNOLDS NO-GO.**  There are finite-dimensional
commutative operator spaces and pairs of order-three Reynolds expectations
whose column has a uniform nonzero Hilbert-space singular-value gap, while
the operator norm, and hence the completely bounded norm, of its
gauge-normal inverse grows at least logarithmically with dimension.

Take a family of finite connected bipartite `3`-regular graphs `G_n` with
uniform edge expansion and girth

```text
g_n >= c log |V(G_n)|.                                  (TRG1)
```

Such high-girth expander families are standard.  Orient every edge from
the left vertex class to the right vertex class and choose a cyclic order
on the three edges at each vertex.  The rotations at the left and right
vertices define permutations `a_n,b_n` of the edge set, each of order
three.  On `l_infinity(E_n)` let

```text
P_a=(I+a_n+a_n^2)/3,       P_b=(I+b_n+b_n^2)/3.        (TRG2)
```

These are precisely the two Reynolds conditional expectations.  Up to the
fixed factor `3` and the sign on the right vertex class, their column

```text
T_n f=(P_a f,P_b f)                                    (TRG3)
```

is the divergence map from oriented edge flows to vertex demands, with a
vertex value repeated on its three incident edges.  Its kernel is the cycle
space and its Hilbert-orthogonal complement is the cut space.  Uniform
expansion gives a uniform lower nonzero singular value of `(TRG3)`.

Let `G_n` denote the Moore--Penrose inverse of `(TRG3)` on the cut space.
Then

```text
G_n T_n=P_(cut,n),                                      (TRG4)
```

where `P_(cut,n)` is electrical routing: it replaces an arbitrary edge
flow by the minimum-energy flow with the same divergence.  Since
`||T_n||_(infinity->infinity)<=1`,

```text
||G_n||_(infinity->infinity)>=||P_(cut,n)||_(infinity->infinity).  (TRG5)
```

The right side is at least a constant times `g_n`.  Here is the elementary
high-girth estimate.  Fix an edge `e=(u,v)`.  The unit `u`-to-`v`
electrical flow is the `e`-th column of `P_(cut,n)`.  Removing `e` leaves a
uniform expander: for large sets this follows by subtracting one edge from
the expansion inequality, and for sets smaller than the expansion
threshold it follows from the tree structure forced by `(TRG1)`.  Hence
the effective resistance from `u` to `v` in `G_n-e` is uniformly bounded,
so a fixed positive fraction of the unit current bypasses `e`.  Every
acyclic path in that bypass has length at least `g_n-1`; decomposing the
electrical flow into paths therefore gives

```text
||P_(cut,n) delta_e||_1 >= c_0 g_n.                    (TRG6)
```

The electrical projection is self-adjoint.  Its maximum absolute row sum
equals its maximum absolute column sum, so `(TRG6)` is exactly

```text
||P_(cut,n)||_(infinity->infinity)>=c_0 g_n.           (TRG7)
```

Combining `(TRG1)`, `(TRG5)`, and `(TRG7)` proves logarithmic divergence.
Realize `l_infinity(E_n)` as the diagonal masa in `M_(|E_n|)` and the two
permutations as permutation unitaries.  The ordinary infinity norm is then
a lower bound for the cb norm at matrix level one, completing the claimed
operator-space counterexample.

This does **not** refute the arithmetic passive gate: its domain is the
additional fixed-`R`, `X`-odd space in
`constrained-reynolds-column-has-a-diagonal-scalar-shadow`.  It does prove
that neither the uniform `L2` angle, finite-dimensional semisimplicity, nor
the fact that both rows are order-three conditional expectations can yield
the desired cb inverse abstractly.  Any positive proof must use a special
arithmetic infinity-Green estimate for that constrained coset complex.

