---
rg: 2
id: kt-two-positive-compressors-generate-full-obstruction-proof
kind: route
title: Generate the Laurent actor with a cyclic permutation times one transvection
target: kt-two-positive-compressors-generate-full-obstruction
requires:
  - monomial-ascending-hnn-coset-action-sofic
  - coordinate-action-not-sofic
  - kun-thom-nonsofic-wreath
  - clifford-compressor-site-growth
  - compressor-growth-index-homomorphism
---

Take `B=I+E_12`, the cyclic coordinate permutation `C`, and `A=CB`.
Properness follows from `B N^3` being the proper cone
`{(n_1+n_2,n_2,n_3)}` and from `C N^3=N^3`.  Recover `C=AB^(-1)`.
Its three conjugates of `B` are the cyclic elementary transvections, and
their three Steinberg commutators are the other elementary directions, so
`<A,B>=SL_3(Z)`.  Every Laurent exponent is the image of `(n,0,0)` under an
integral unimodular matrix; hence the `SL_3(Z)`-conjugates of the polynomial
elementary group generate the Laurent elementary group.  Thus
`<Gamma,A,B>=G`.

Apply one-compressor action soficity separately to `A` and `B`.  A common
exhausting family of joint finite permutation tables would make the full
coset action sofic, and a common family including all finite lamp tables
would make the binary wreath sofic.  The two established nonsoficity results
exclude these families; negating the approximation definition supplies a
finite table with a positive uniform error floor.  Finally, the two strict
compressors have infinite Clifford growth index, while `C` has index one,
so the exact index relation is consistent and cannot provide the missing
unitary-HS upgrade.
