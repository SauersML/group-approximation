---
rg: 2
id: literal-mark-quotient-finite-residual-proof
kind: route
title: Level collapse in finite quotients plus folding of the free lamplighter
target: literal-mark-quotient-finite-residual
requires: [literal-lamp-kernel-clifford-block-amalgam, finite-quotient-blindness]
artifacts:
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
---

## Direct proof

*Level collapse.*  For `phi` into a finite group, blindness gives
`phi(Gbar_k) = phi(Gbar)` for all `k`, hence `phi(T) = phi(Gbar)` and
`T <= Gbar . ker phi`.  Conjugating by `g` with `x = g Gbar` and using
normality of `ker phi` gives `T <= Stab_V(x) . ker phi`; writing
`h = sigma k` accordingly, `phi(c_{hx}) = phi(sigma) phi(c_x) phi(sigma)^{-1}
= phi(c_x)`.  Levels are `T`-orbits, so all same-level lamps agree and
`R <= ker phi`.  The argument never uses commutativity of the lamp kernel.

*The collapse quotient.*  Identifying the eight lamps of a block collapses
`(Z/2)^8` to `Z/2`, and identifying blocks of a common level amalgamates
those factors, so the free product becomes `*_{n in Z} Z/2`, with `T` acting
trivially and `tau` shifting.

*Residual finiteness.*  Elements with nontrivial `V`-part are separated by
Malcev, `V` being finitely generated linear.  A reduced word in the `xi_n`
using levels within a window of width `< m` stays reduced after folding `Z`
to `Z/m`, and `( *_{Z/m} Z/2 ) semidirect Z/m` is finitely generated
virtually free, hence residually finite.  Section 9 of the cited note is the
complete argument.
