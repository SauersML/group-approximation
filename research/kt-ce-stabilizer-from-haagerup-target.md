---
rg: 2
id: kt-ce-stabilizer-from-haagerup-target
kind: route
title: Dead — realize the Kun--Thom stabilizer inside a Haagerup target
target: kt-subgroup-is-a-ce-commutation-stabilizer
requires: []
---

**Dead.** The approach: map `G` into a finite von Neumann algebra where
Connes embeddability is automatic and the Kazhdan image is tame — the
hyperfinite factor or an amenable algebra (half-space tensor chains, shift
crossed products `R rtimes Z`), a free group factor, or an amalgamated free
product over amenable subalgebras — and find there an element whose
commutation stabilizer is exactly `Gamma`.

Invalidated by `haagerup-targets-carry-no-relative-wall`: when
`sigma(Gamma)''` has the Haagerup property it is purely atomic
(`kazhdan-images-in-haagerup-algebras-are-atomic`), every compressor then fixes
the relative commutant (`fd-isotypic-part-of-a-kazhdan-image-carries-no-wall`),
and a non-normal infranormal Kazhdan subgroup cannot be a commutation
stabilizer.
