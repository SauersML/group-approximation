---
rg: 2
id: classwide-hyperbolic-kazhdan-hs-stability-covers-fp-kazhdan
kind: claim
title: Flexible HS stability of every hyperbolic Kazhdan group would make every finitely presented Kazhdan group stable
distinct_from:
  kazhdan-hyperbolic-b2-group-flexibly-hs-stable: that asks for one flexibly stable hyperbolic Kazhdan group with b_2 >= 1; this shows that a stability theorem for all hyperbolic Kazhdan groups, or for any class closed under Belegradek--Osin covers, already contains stability of every finitely presented Kazhdan group.
  hyperbolic-kazhdan-cover-of-leavitt-unit-group: that constructs one hyperbolic Kazhdan cover with a Kazhdan kernel; this uses the general construction as a screen on class-wide stability arguments.
artifacts:
  - research/artifacts/kazhdan-hyperbolic-hs-candidates-2026-09-12.md
---

**ESTABLISHED.** If every word-hyperbolic group with property (T) is flexibly
Hilbert--Schmidt stable, then every finitely presented group with property (T) is
flexibly HS stable. Consequently:

- every finitely presented hyperlinear Kazhdan group is residually finite;
- every infinite finitely presented minimally almost periodic Kazhdan group is not
  hyperlinear. Two instances:
  - the binary Leavitt unit group. It is finitely presented, and it has property (T), since (TT)/T, `binary-leavitt-unit-group-has-tt-mod-t`, bounds every cocycle into a representation without invariant vectors, and the group is perfect.
  - the Caprace--Rémy simple Kazhdan lattices of `simple-kazhdan-kac-moody-lattices-exist`.

**Use as a screen.** Suppose a proof of flexible HS stability works for a class of
hyperbolic Kazhdan groups that is closed under the Belegradek--Osin construction.
That proof settles `non-hyperlinear-group` on its own. So a stability argument for
the candidates of `kazhdan-hyperbolic-b2-group-flexibly-hs-stable` must either use
something that Belegradek--Osin covers lack, or be a proof of non-hyperlinearity in
disguise.

DERIVATION
classwide-hyperbolic-kazhdan-hs-stability-proof
