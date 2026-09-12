---
rg: 2
id: binary-affine-support-classical-propagation-proof
kind: route
title: Reduce every safe support to unary and parity constraints and propagate bits
target: binary-affine-safe-perfect-support-forces-classical-satisfaction
requires:
  - functional-support-is-affine-exactly-on-an-affine-domain-map
---

Put `A_x=P_x^0-P_x^1` and `B_y=Q_y^0-Q_y^1`.  Every nonempty affine subset
of the Boolean square is cut out by a consistent collection of equations of
the following forms:

```text
a=c,                 b=c,                 a+b=c.       (BAP1)
```

The full square imposes no equation.  Since the perfect strategy has zero
weight outside `S_e`, it has zero weight outside `Aff(S_e)`.  Consequently a
constraint of the three types in `(BAP1)` gives respectively the vector
identities

```text
A_x xi=(-1)^c xi,     B_y xi=(-1)^c xi,
A_x xi=(-1)^c B_y xi.                              (BAP2)
```

Consider the ordinary Boolean constraint system consisting of all equations
cutting out the sets `Aff(S_e)`.  It is just a bipartite graph of parity edges
plus unary pinned bits.  If it were inconsistent, propagation in one connected
component would either encounter two contradictory unary pins or a cycle of
odd total parity.  Applying the corresponding chain of identities `(BAP2)`
would give `xi=-xi`, impossible.  Therefore the affine system has a classical
solution.  On each edge its pair lies in `Aff(S_e)`, which lies in `R_e` by
the safety assumption, so this solution wins the original game perfectly.

For the minimal-fiber statement, a set with at most two points in `F_2^2` is
an affine point or affine line.  The affine hull of any three distinct points
is the whole square.  Since `S_e subseteq R_e`, failure of `(BAS1)` is therefore
possible only when `S_e` consists of three points and `R_e=S_e`; supports of
four points force `R_e=F_2^2` and are safe.  Finally, a partial function on a
binary domain has a graph of size at most two, proving the projection
specialization.
