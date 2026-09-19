---
rg: 2
id: independent-row-masks-transfer-bcs-gap-to-ambient-identity
kind: claim
title: Independent row masks transfer a finite BCS gap to the ambient identity Gram vector
distinct_from:
  high-density-local-sectors-force-one-bcs-gram: that intersects context sectors and pays the meet deficit; this uses no meet and permits a different mask for every predicate and consistency row.
  common-meet-local-sectors-pay-one-deficit: that is sharper when a large common meet is authenticated; this instead pays the weighted codimension of each row separately.
  one-gram-vector-decodes-a-finite-bcs-strategy: that lower-bounds the energy for a supplied Gram operator; this upper-bounds the special ambient energy at G=I using unrelated row masks.
---

Fix a finite BCS game `B` with finite-dimensional value at most `1-Delta`,
`Delta>0`.  Let `P_(c,a)` be one context PVM for every context, put

```text
F_c=sum_(a forbidden)P_(c,a),
A_(c,x)=sum_a a_x P_(c,a),
```

and let `B_x` be one self-adjoint involution for every shared variable.
Write `mu_(c,x)` for the question distribution and
`mu_c=sum_(x in U_c)mu_(c,x)`.

Choose arbitrary projections `q_c^pred` and `q_(c,x)^con`; they need not
commute, agree, or have a nonzero common meet.  Define

```text
delta_c^pred=tr(1-q_c^pred),
delta_(c,x)^con=tr(1-q_(c,x)^con),

eta_c^pred=||F_c q_c^pred||_2,
eta_(c,x)^con=(1/2)||(A_(c,x)-B_x)q_(c,x)^con||_2.     (IRM1)
```

Then every finite matrix tuple satisfies

```text
Delta
 <=sum_c mu_c(eta_c^pred+sqrt(delta_c^pred))^2
   +sum_(c,x)mu_(c,x)
      (eta_(c,x)^con+sqrt(delta_(c,x)^con))^2.          (IRM2)
```

In particular, exact row identities

```text
F_c q_c^pred=0,
(A_(c,x)-B_x)q_(c,x)^con=0                            (IRM3)
```

force the weighted codimension bound

```text
Delta
 <=D_row:=sum_c mu_c tr(1-q_c^pred)
          +sum_(c,x)mu_(c,x)tr(1-q_(c,x)^con).         (IRM4)
```

The freedom is only in the masks.  The context PVMs and shared-variable
involutions remain one global tuple; replacing them independently from row
to row would not define the ambient BCS strategy used by the gap.

