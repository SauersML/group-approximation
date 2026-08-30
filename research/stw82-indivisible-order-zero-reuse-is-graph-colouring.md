---
rg: 2
id: stw82-indivisible-order-zero-reuse-is-graph-colouring
kind: claim
title: Indivisible order-zero colour reuse is exactly graph colouring of support overlap
distinct_from:
  stw82-order-zero-direct-sum-support-criterion: that treats one pair of order-zero maps; this computes the exact minimum number of global colours for an arbitrary finite family.
  stw82-raw-two-cut-reuse-iff-quasidiagonal: that globalizes complementary two-cut perturbability along an extension; this allows arbitrary support patterns but keeps each input colour indivisible.
---

Let `V` be finite and, for each `v in V`, let `F_v` be a unital C*-algebra
and

```text
phi_v:F_v -> B
```

a cpc order-zero map.  Form the support-overlap graph `G_phi` on `V` by
putting an edge between distinct `v,w` exactly when

```text
phi_v(1) phi_w(1) != 0.                               (G1)
```

For a partition `V=C_0 disjointUnion ... disjointUnion C_r`, define

```text
Phi_j : directSum_(v in C_j) F_v -> B,
Phi_j((x_v)_v)=sum_(v in C_j) phi_v(x_v).              (G2)
```

Then all `Phi_j` are cpc order zero if and only if every `C_j` is an
independent set of `G_phi`.  Consequently the least number of global
order-zero colours obtainable by relabelling and directly summing the
given maps, without splitting or changing any `phi_v`, is exactly

```text
chi(G_phi).                                           (G3)
```

In particular, exact reuse into two global colours is possible precisely
when the support-overlap graph is bipartite.  This is an exact obstruction
for fixed outgoing colours, not an obstruction to other nuclear-dimension
approximations which split, perturb, or replace those maps.

Consequently, suppose `A` admits arbitrarily accurate finite-dimensional
approximations

```text
A -psi-> directSum_(v in V) F_v -sum_v phi_v-> A       (G4)
```

in which `psi` is cpc, every `phi_v` is cpc order zero, and every resulting
support graph is `(r+1)`-colourable.  Regrouping the same finite-dimensional
summands along a graph colouring turns (G4) into an `r`-dimensional nuclear
approximation.  Hence `dim_nuc(A)<=r`.  No extra colour is introduced.
