---
rg: 2
id: leavitt-permutation-cover-impossibility-proof
kind: route
title: A permutation atlas would produce a forbidden sofic central cover
target: leavitt-regular-atlas-permutation-cover-impossible
requires:
  - leavitt-all-countable-central-covers-are-nonsofic
  - leavitt-regular-atlas-hyperlinearity-criterion
---

Assume such permutation charts exist. Their metric ultraproduct gives a
homomorphism

```text
Phi: U_Q = (A_8*A_8)/<<bar S>> -> product_omega Sym(Omega_n).
```

It is nontrivial: every nonidentity element of the first `A_8` chart moves
every point, so its ultraproduct Hamming distance from the identity is one.
The atlas criterion identifies `U_Q` as a quasisimple universal central
extension of the simple group `Q`. Hence `ker(Phi) <= Z(U_Q)`. Its image is
therefore a countable central extension of `Q` and is sofic as a subgroup of a
permutation metric ultraproduct. This contradicts
`leavitt-all-countable-central-covers-are-nonsofic`.

Notice why quotient permanence is not being smuggled in: the contradiction is
with the special theorem that the image central extension itself is nonsofic,
not with nonsoficity of its quotient `Q`.
