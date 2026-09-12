---
rg: 2
id: substituted-elementary-subgroup-is-not-infranormal
kind: claim
title: A proper monomial substitution of the Kun--Thom elementary group is not infranormal in it
distinct_from:
  kt-intermediate-coset-wreaths-are-nonsofic: that extends nonsoficity to intermediate index sets over the whole Kazhdan group G; this shows that inside Gamma the one-compressor subgroup gives no infranormal pair, so Theorem A does not certify the Gamma-orbit wreath
  one-letter-wreath-support-reduces-to-gamma-orbit-wreaths: that reduces one-letter supports to Gamma-orbit wreaths; this settles that the natural orbit stabilizer is not infranormal
---

**ESTABLISHED.** Let `R_+ = F_q[x_1..x_d]`, `r >= 2`, and let `t` act by a
nonnegative monomial substitution `A` in `SL_d(Z)` whose image
`S = F_q[x^(a_1),...,x^(a_d)]` is a proper subring of `R_+`. Then
`t Gamma t^(-1) = EL_r(S)` is not infranormal in `Gamma = EL_r(R_+)`.

Its compression semigroup lies inside the normalizer
`{gamma : gamma M_r(S) gamma^(-1) = M_r(S)}`. That normalizer is a proper
subgroup, since `e_12(f)` with `f` outside `S` is not in it.

So Kun--Thom Theorem A does not certify the orbit wreath
`(Z/2) wr_(Gamma / t Gamma t^(-1)) Gamma` nonsofic. Lamp corners over `Gamma`
plus one such letter have no certified nonsofic support. A certified support
needs compressing letters generating `SL_d(Z)`, for instance the nonnegative
elementary matrices. With `Gamma` they generate all of `G`, which is Kun--Thom's
own pair.
