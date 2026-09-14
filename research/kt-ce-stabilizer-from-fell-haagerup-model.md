---
rg: 2
id: kt-ce-stabilizer-from-fell-haagerup-model
kind: route
title: Dead — witness the Kun--Thom stabilizer in a canonical Fell model with a Haagerup coefficient
target: kt-subgroup-is-a-ce-commutation-stabilizer
requires: []
---

**Dead.** The approach: take a tame coefficient representation
`pi : G -> U(M_0)`, for instance through an amenable algebra or a free group
factor, tensor it with the regular representation to obtain the canonical model
`lambda tensor pi`, and look for a stabilizer witness in the larger,
non-Haagerup algebra `L(G) tensor-bar M_0`, which contains `L(Gamma)`.

Invalidated by `kt-fell-models-over-haagerup-coefficients-are-wall-free`.
Because the polynomial subgroup has infinite conjugacy classes, the relative
commutant of the Fell model is `1 tensor` that of the coefficient
(`fell-models-inherit-walls-from-coefficients`). The Haagerup no-wall theorem
applies there.
