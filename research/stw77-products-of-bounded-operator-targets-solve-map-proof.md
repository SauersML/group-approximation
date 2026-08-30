---
rg: 2
id: stw77-products-of-bounded-operator-targets-solve-map-proof
kind: route
title: Assemble essential-representation absorbers coordinatewise
target: stw77-products-of-bounded-operator-targets-solve-map
requires:
  - stw77-bounded-operator-target-case
  - oinfty-map-stability-is-central-isometry-splitting
---

Write `phi_lambda` for the composition of `phi` with evaluation at
coordinate `lambda`. Proper infiniteness passes through homomorphisms.
Consequently, whenever `phi_lambda(a)` is nonzero for `a>=0), it is
properly infinite in `B(H_lambda)`: apply coordinate evaluation to the
properly infinite product element `phi(a)`.

Thus every `phi_lambda` satisfies the bounded-operator target theorem. Fix a
finite set `F subset A` and `epsilon>0`. For each `lambda`, that theorem
provides isometries

```text
s_(lambda,1),s_(lambda,2) in B(H_lambda)
```

with orthogonal ranges and

```text
max_(a in F,t=1,2)
 ||[s_(lambda,t),phi_lambda(a)]|| < epsilon.
```

Set `s_t=(s_(lambda,t))_lambda`. These are elements of the C*-product,
satisfy `s_t^*s_u=delta_(t,u)1), and obey

```text
max_(a in F,t=1,2)||[s_t,phi(a)]||
 = max_(a in F,t=1,2) sup_lambda
   ||[s_(lambda,t),phi_lambda(a)]||
 <= epsilon.
```

Using `epsilon/2` in the coordinate choices gives a strict
`epsilon` bound if desired. Hence every finite-set centralization defect
vanishes, and the central-isometry criterion gives O-infinity-stability.
