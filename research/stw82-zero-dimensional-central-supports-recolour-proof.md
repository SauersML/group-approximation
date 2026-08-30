---
rg: 2
id: stw82-zero-dimensional-central-supports-recolour-proof
kind: route
title: Refine the common spectrum by clopen blocks and match active supports independently
target: stw82-zero-dimensional-central-supports-recolour-pointwise
requires:
  - stw82-order-zero-direct-sum-support-criterion
---

Fix `epsilon>0`.  For `x in X`, put

```text
A_x={v:h_v(x)>0}.
```

By (Z1), `|A_x|<=m`.  Continuity and finiteness of `V` give an open
neighbourhood `U_x` of `x` on which

```text
h_v(y)<epsilon                    (v notin A_x).      (P1)
```

Choose a finite subcover of `(U_x)_(x in X)`.  A finite open cover of a
compact zero-dimensional space has a finite pairwise disjoint clopen
refinement: choose finitely many clopen sets refining the cover and take the
atoms of the finite Boolean algebra they generate.  Denote the resulting
partition by `(P_j)_(j=1)^N`, and choose `x_j` with `P_j subseteq U_(x_j)`.

For every `j`, choose an injection

```text
sigma_j:A_(x_j)->{1,...,m}.
```

Define

```text
c_(v,k)=sum_{j: v in A_(x_j), sigma_j(v)=k} 1_(P_j). (P2)
```

These are projections in `C`.  For fixed `j,k`, injectivity assigns the
block `P_j` to at most one `v`; hence (Z2) holds.  For a fixed `v`, the sum
over `k` of (P2) is the characteristic function of the union of those
blocks for which `v in A_(x_j)`.  On every omitted block, (P1) bounds `h_v`
by `epsilon`.  The blocks are disjoint, so functional calculus gives (Z3).

Every cutter commutes with every outgoing range.  Therefore (Z4) is cpc
order zero and its unit support is `c_(v,k)h_v`.  For fixed `v`, the
projections `(c_(v,k))_k` are orthogonal, so

```text
s_v=sum_k c_(v,k)
```

is a projection commuting with `phi_v(F_v)`.  Hence

```text
phi_v-sum_k psi_(v,k)=(1-s_v)phi_v
```

is a positive order-zero map.  The norm of a positive map from a unital
C*-algebra is the norm of its value at the unit, and therefore

```text
norm(phi_v-sum_k psi_(v,k))=norm((1-s_v)h_v)<epsilon.
```

This proves (Z5).  Equivalently, the same equality follows from the
supporting-homomorphism formula `phi_v(a)=pi_v(a)h_v`.
For fixed `k`, (Z2) makes the supports belonging to distinct `v`
orthogonal, so the order-zero direct-sum support criterion proves that the
fixed-label sum is cpc order zero.

To prove optimality, choose `x` at which the maximum in (Z1) is attained
and put

```text
gamma=min_(v in A_x) h_v(x)>0.
```

For a `C`-valued cover with error below `gamma/2`, evaluation at `x` shows
that, for every `v in A_x`, at least one cutter `c_(v,k)(x)` is positive.
Same-label orthogonality says that one label can be positive for at most
one such `v`.  Thus the labels inject `A_x` into `{1,...,d}`, and `d>=m`.

Now assume the finite-dimensional central hypothesis (Z6).  On the atom
`z_j`, write

```text
h_v z_j=lambda_(v,j) z_j.
```

Choose an injection from the active vertices at each atom into
`{1,...,m_0}` and use (P2), with the `z_j` in place of the clopen blocks.
Every active atom is retained, so the resulting central projection cover is
exact.

For the converse, let arbitrary positive contractions `c_(v,k) in M(B)`
give an exact `d`-label cover.  Fix `j`.  Centrality of `z_j` preserves
positivity and orthogonality after compression.  For every active `v`, the
cover identity and `lambda_(v,j)>0` give

```text
sum_k z_j c_(v,k) z_j=z_j.                           (P4)
```

Apply any state on the unital corner `z_j M(B)`.  Summing (P4) over the
active `v`, while using that for fixed `k` the compressed cutters are
pairwise orthogonal positive contractions with sum at most `z_j`, gives

```text
|{v:z_jh_v!=0}|<=d.
```

Taking the maximum over `j` proves the asserted optimality against arbitrary
cutters.

For the nuclear-dimension consequence, start with an approximation accurate
to `epsilon/2`, apply the construction to its outgoing maps with error
`epsilon/2`, and regroup the finite-dimensional summands by the `r+1`
labels.  The first cpc map is unchanged and the new outgoing map has
`r+1` order-zero colours, proving (Z7).

In the displayed example, use the assignments

```text
at a:  1->1, 2->2;
at b:  2->1, 3->2;
at c:  3->1, 1->2.
```

Equivalently,

```text
c_(1,1)=e_a, c_(1,2)=e_c,
c_(2,1)=e_b, c_(2,2)=e_a,
c_(3,1)=e_c, c_(3,2)=e_b.
```

This is an exact two-label coupled cover although the three unsplit supports
form an odd cycle.
