---
rg: 2
id: constant-size-private-basins-give-uniform-root-control
kind: claim
title: Constant-size private basins give uniform same-Hilbert root control
distinct_from:
  bounded-degree-clouds-have-logarithmic-root-gauge-leak: that treats growing bounded-degree basins and proves rooted control fails; this fixes one finite basin and obtains a uniform positive estimate.
  expander-cloud-reduction-preserves-pauli-dimension-gap: that replaces high-degree logical equality classes by growing expanders; this uses only constant-size basins at already bounded-occurrence selected labels.
  equality-synchronized-lifts-create-two-pair-contours: that repeats a logical mixed pair across two equality copies; this attaches the unique mixed edge only to the root of each basin.
---

Fix a finite connected rooted graph `(H,rho)` and an anchor `a in V(H)`.
For each private sample `t`, take a disjoint copy `H_t`.  If reflections or
unitaries `U_(t,v)` act on one Hilbert space, then

```text
(1/K) sum_t ||U_(t,rho)-U_(t,a)||_2^2
 <= C_H (1/(K|E(H)|)) sum_t sum_(uv in E(H))
                         ||U_(t,u)-U_(t,v)||_2^2,             (CPB1)
```

where one may take `C_H=dist_H(rho,a)|E(H)|`.  The estimate is in the
original matrix dimension and is valid for arbitrary operator assignments.

Attach the one private mixed X--Z edge for sample `t` only to the two roots
of its X and Z basins.  Then every selected root has fixed positive density
`1/|V(H)|` in its basin, total basin size is `K|V(H)|=O(K)`, degrees remain
bounded, and the mixed graph is still a matching.  Hence no mixed rectangle
is created inside a basin and no mixed pair is repeated.  A contour using
two different basins can still be created by the downstream X- and Z-code
incidence and must be excluded by that code's placement theorem.  If the
anchors are decoded on the same Hilbert space by a bounded-occurrence
additive code, `(CPB1)` transfers
that decoder to the private Weyl roots with dimension-independent loss.

This is the exact positive counterpart of the logarithmic root-gauge leak.
It cannot rescue dense BLR degree reduction: if one logical selected label
has `M_r` occurrence copies in its equality basin, its unique mixed port has
density `1/M_r`; fixed positive rooted weight forces `sup_r M_r<infinity`.
The surviving architecture must therefore test the selected `O(r^2)` labels
directly with bounded occurrence, rather than copy them through the full
`2^r`-point BLR table.
