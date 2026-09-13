---
rg: 2
id: simple-kazhdan-lef-group-c-star-fails-llp-proof
kind: route
title: A hyperlinear non-residually-finite Kazhdan group cannot have an LLP full C*-algebra
target: simple-kazhdan-lef-group-c-star-fails-llp
requires: [simple-kazhdan-lef-group-from-minimal-subshift, llp-non-rf-kazhdan-group-is-non-hyperlinear]
---

`S` is infinite and simple, so every finite quotient is trivial and `S` is not residually finite.
By the first prerequisite, `S` is Kazhdan and LEF, hence hyperlinear. If `C*(S)` had the LLP, the
second prerequisite would make `S` non-hyperlinear, a contradiction. So `C*(S)` fails the LLP.

For the factorization property: Kirchberg's theorem, recalled as Theorem 1.1 of Thom
arXiv:0810.2180, says a Kazhdan group has the factorization property iff it is residually finite.
`S` is not residually finite, so it lacks the factorization property.
