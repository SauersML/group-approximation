---
rg: 2
id: signed-reynolds-marked-complement-proof
kind: route
title: Untwist the signed source by the disjoint marked involution
target: signed-reynolds-detectors-form-the-marked-complement-subgroup
requires:
  - center-chain-mixed-hecke-overlap-is-common-pauli-source
  - full-leavitt-idempotent-defect-saturation
---

Every displayed generator of `L_0` has root indices in
`{2,4,5,6,7,8,9}`, while `z=x_13(q)`.  The Steinberg commutator relations
therefore make `z` commute with `L_0`.  The elementary-matrix image of
`L_0` fixes coordinates `1` and `3` pointwise, whereas the image of `z` is
the nonidentity transvection `I+qE_13`.  The second prerequisite gives
`q!=0` and hence `z!=1`.  Thus `<z> intersect L_0={1}`, proving `(RDC3)`.

Because `lambda_0` is a character, `epsilon:L_0->F_2` is a homomorphism.
Centrality of `z` relative to `L_0` gives

```text
theta(g)theta(h)
 =z^(epsilon(g)+epsilon(h))gh
 =z^epsilon(gh)gh
 =theta(gh).                                           (1)
```

Projection to the `L_0` factor in `(RDC3)` makes `theta` injective.  Direct
evaluation of `mu(theta(g))` gives one, and both `R_0` and `ker(mu)` have
index two in `<z> directProduct L_0`; hence they agree.  This proves
`(RDC4)--(RDC6)`.

On the negative marked sector,

```text
z^epsilon(g)P_z=(-1)^epsilon(g)P_z=lambda_0(g)P_z.     (2)
```

Averaging `(2)` over `g` proves `(RDC8)`.

Finally `R_0` is a finite `2`-group.  Every `r_g!=1` therefore has even
order.  In the left regular representation its restriction to every left
coset of `<r_g>` contains all roots of unity of that even order, including
`-1`, so `||lambda(r_g)-I||_op=2`.  On the `z=-1` summand of the regular
representation of `<z> directProduct L_0`, the operator `lambda(r_g)` is
`lambda_0(g)` times the regular permutation by `g`.  If
`lambda_0(g)=+1`, even order supplies eigenvalue `-1`; if
`lambda_0(g)=-1`, the regular permutation supplies eigenvalue `+1`, which
becomes `-1` after the sign.  Thus the compressed norm in `(RDC9)` is also
two.
