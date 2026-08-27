---
rg: 2
id: signed-orbit-averaging-does-not-divide-green-cost
kind: claim
title: Signed orbit averaging compresses the full Green operator without an orbit-size gain
distinct_from:
  constrained-reynolds-column-has-a-diagonal-scalar-shadow: that extracts the signed arithmetic column; this compares its Moore--Penrose inverse exactly with the unconstrained A/B incidence Green operator.
  proper-torus-reynolds-is-edge-refinement: that identifies the extra edge labels and missing triangle lifts; this rules out a proposed electrical-routing shortcut based only on the large cyclic orbit.
  right-u-reynolds-has-torus-hecke-blocks: that decomposes the restricted column harmonically; this gives the equivalent real-space compression formula and isolates the missing congestion estimate.
---

**ESTABLISHED; ROUTING NO-GO.**  Let `D_Q` be the two-row order-three
incidence operator `(DSS3)` before imposing the fixed-`H`, Weyl-odd input
condition, and let

```text
P_chi=|N|^(-1) sum_(n in N) conjugate(chi(n)) L_n,
N=<H,w>,       chi|_H=1,       chi(w)=-1.              (SOG1)
```

Thus the arithmetic scalar column is

```text
C_H=D_Q|_(ran P_chi).                                  (SOG2)
```

The normal operator `D_Q^*D_Q` commutes with `P_chi`: equivalently, the
signed tangent space is reducing for the normal operator, as proved in
`constrained-reynolds-column-has-a-diagonal-scalar-shadow`.  Functional
calculus for the Moore--Penrose inverse therefore gives the exact
compression formula

```text
C_H^dagger=P_chi D_Q^dagger                            (SOG3)
```

on `ran(C_H)` (with the natural inclusion into `ran(D_Q)`).  More
explicitly,

```text
(C_H^*C_H)^dagger C_H^*
 =P_chi (D_Q^*D_Q)^dagger D_Q^*.                       (SOG4)
```

Since `(SOG1)` is a signed average of infinity isometries,

```text
||P_chi||_(infinity -> infinity)<=1.                   (SOG5)
```

Consequently any uniform full-graph Green bound transfers to the signed
column:

```text
||C_H^dagger||_(infinity -> infinity)
 <=||D_Q^dagger||_(infinity -> infinity).              (SOG6)
```

There is, however, no factor `1/|H|` in `(SOG5)--(SOG6)`.  This is sharp
at the level of orbit averaging: on the `chi`-isotypic range,
`P_chi x=x`, so its infinity norm is exactly one whenever that range is
nonzero.  Even the identity operator on a nonzero `chi`-space refutes a
formal estimate `||P_chi||<=C/|H|` as `|H|` grows.

The same obstruction appears in electrical routing.  If a path flow `J`
of length/cost `L` is symmetrized as

```text
J_chi=|H|^(-1) sum_(h in H) chi(h) hJ,                 (SOG7)
```

then the triangle inequality gives cost at most `L`, not `L/|H|`.
In fact, disjoint support gives the opposite of the hoped-for conclusion:
if the supports of the translates `hJ` are pairwise disjoint, then

```text
||J_chi||_1
 =|H|^(-1) sum_(h in H)||hJ||_1
 =L.                                                    (SOG8)
```

Thus disjointness preserves the whole routing cost.  An orbit-size gain
requires a separate **signed cancellation on overlapping translates**;
small congestion or large orbit cardinality alone does not provide it.
The arithmetic inequality

```text
ord_p(4)>=log_4 p
```

controls the number of translates but says nothing about this overlap.

Therefore the proposed estimate

```text
electrical cost = O(log|Q|/|H|)
```

does not follow from symmetrization and order growth.  A viable proof may
still use `(SOG3)`, but it must prove either a uniform infinity Green bound
for the full `A/B` incidence operator or an arithmetic congestion theorem
for the specific translated routings.  Orbit averaging alone supplies
neither, and this claim does not assert that the proper-torus Green norms
diverge.
