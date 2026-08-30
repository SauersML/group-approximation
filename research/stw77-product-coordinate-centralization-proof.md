---
rg: 2
id: stw77-product-coordinate-centralization-proof
kind: route
title: Solve every simple coordinate and assemble the central isometries with a uniform tolerance
target: stw77-products-of-simple-comparison-targets-solve-map
requires:
  - oinfty-map-stability-is-central-isometry-splitting
  - stw78-simple-comparison-targets-force-oinfinity-stability
---

Let `q_lambda:B->B_lambda` be the coordinate map and set
`phi_lambda=q_lambda phi`.  Proper infiniteness passes through star
homomorphisms, so every `1_(B_lambda)=q_lambda(1_B)` is properly infinite.
It follows that `B_lambda` has no normalized `2`-quasitrace.  Indeed, if
`p_1,p_2<=1_(B_lambda)` are orthogonal projections each Murray--von Neumann
equivalent to the unit, normalized quasitracial invariance and orthogonal
additivity would give

```text
1 >= tau(p_1+p_2)=tau(p_1)+tau(p_2)=2.
```

Finite nuclear dimension implies that `phi` is nuclear, and nuclearity
passes to each coordinate `phi_lambda`.  The simple comparison-target
theorem therefore applies: each `phi_lambda` is strongly O-infinity-stable,
hence O-infinity-stable.

It remains to pass back from all coordinates to the product; this is not a
formal converse to quotient descent.  Fix a finite set `F subset A` and
`epsilon>0`.  The central-isometry characterization applied to
`phi_lambda` gives, for every `lambda`, isometries

```text
s_(1,lambda),s_(2,lambda) in B_lambda
```

with orthogonal ranges and

```text
max_(a in F,r=1,2)
  norm([s_(r,lambda),phi_lambda(a)]) < epsilon/2.      (1)
```

Choose such a pair in every coordinate and put

```text
s_r=(s_(r,lambda))_lambda in B,       r=1,2.
```

Coordinatewise multiplication gives exact product relations

```text
s_r^*s_t=delta_(r,t)1_B.
```

Taking the supremum of the coordinate norms in (1) gives

```text
max_(a in F,r=1,2) norm([s_r,phi(a)]) <= epsilon/2.
```

Thus every finite-set centralization defect of `phi` vanishes.  The central
isometry characterization supplies a unital embedding

```text
O_infinity -> B_omega intersect phi(A)',
```

so `phi` is O-infinity-stable.

For example, this applies to arbitrary products of simple purely infinite
or simple Z-stable properly infinite factors.  Infinite products exhibit
the genuinely nonsimple, generally nonseparable target geometry not covered
by the one-factor theorem.
