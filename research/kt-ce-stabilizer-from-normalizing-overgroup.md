---
rg: 2
id: kt-ce-stabilizer-from-normalizing-overgroup
kind: route
title: Dead — witness the Kun--Thom stabilizer by an element normalizing the group
target: kt-subgroup-is-a-ce-commutation-stabilizer
requires: []
---

**Dead.** The approach: use an overgroup on which hyperlinearity permanence is
free and pick a witness there that normalizes `G` —
- the amenable extension `G rtimes K` with witness `k in K` (centralizer = the
  fixed subgroup of an automorphism),
- a direct factor,
- or a unitary implementing an automorphism of an injective image `sigma(G)`,
aiming for `C_G(witness) = Gamma`.

Invalidated by `kt-normalizing-witnesses-centralize-compressors`: such a
witness commutes with every compressor because `C_G(Gamma) = 1`, hence with
all of `G`.
