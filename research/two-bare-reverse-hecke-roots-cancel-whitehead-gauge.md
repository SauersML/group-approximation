---
rg: 2
id: two-bare-reverse-hecke-roots-cancel-whitehead-gauge
kind: route
title: Multiply two bare reverse-Hecke roots to cancel the Whitehead gauge
target: el20-six-moving-coefficient-square-bridges
requires:
  - paired-critical-opposite-roots-return-only-trivially
---

This route proposed replacing the same-channel pair by two bare root
letters obtained by reversing two distinct directed roots in the Hecke
actor `L_0`.  Their
product was intended to leave the source atom, return as a nonidentity
normalizer, and supply the inverse reservoir action of the literal
Whitehead.

It is invalidated by
`two-distinct-reverse-hecke-roots-cannot-return`.  The intrinsic
fixed-space filtration of `L_0` is preserved by every normalizer, while
each bare reverse-root letter strictly raises the filtration.  For two
distinct displayed arrows the first raised coordinate cannot cancel; exact return
forces both coefficients to vanish.  Hence no nonidentity returned
normalizer exists, and reservoir cancellation is never reached.

The invalidation does not apply to the eight external normalizers of
`signed-hecke-normalizer-has-eight-external-root-returns`: their Leavitt
realizations are two-channel coefficient commutators through a spare
coordinate, not products of two bare reverse-Hecke roots.  It also does not
apply to a longer word or to an intervening coefficient/Whitehead
occurrence.


