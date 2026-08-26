---
rg: 2
id: order-seven-head-return-conjugacy-audit-proof
kind: route
title: Enumerate the signed-L0 root orbits and the complete depth-two B2 return table
target: signed-l0-does-not-attach-cross-returns-to-order-seven-head
requires:
  - cross-whitehead-sandwiches-branch-roots-into-signed-normalizer
  - native-whitehead-hecke-head-has-order-seven-anchor
  - fused-authenticated-cross-returns-retain-s3-square-gauge
---

Represent the actor coordinates in the order `(2,4,5,6,7,8,9)`.  A
constant root is the corresponding rank-one transvection over `F_2`.
Breadth-first closure of the ten signed-`L_0` generators has exactly `8192`
matrices.  Store a shortest generator word for each matrix, form its inverse
by reversing that involutory word, and compare

```text
g x_(t,s)(1) g^(-1)                                   (OHCP1)
```

against every one of the `42` elementary transvections.  This proves the
zero-hit assertions and the singleton elementary orbit intersections in
`(OHC3)--(OHC4)`; it also gives the singleton `{4->8}` for `B_2`.

For the coefficient audit, use exact binary-prefix replacement normal
forms and enumerate the `48` nonidentity monomials `s_mu t_nu` with
`|mu|,|nu|<=2`.  Multiply each `K_i x_(8,k)(g) K_i` exactly and retain only
matrices equal to the identity plus one root with coefficient `b_2`.
Across `2*2*48=192` cases the four rows in `(OHC6)` are the complete list.
The second follows directly from

```text
p(s_10t_1)=s_00t_1,        r(s_10t_1)=0.              (OHCP2)
```

Finally apply the already enumerated position orbits to both positions in
`(OHC6)`.  Since neither reaches `4->8`, the native order-seven head factor
has not been occurrence-authenticated.
