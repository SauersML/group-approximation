---
rg: 2
id: marked-quotients-not-lef
kind: claim
title: The marked quotients admit no exact finite models
invalidates:
  - commuting-lamp-quotient-via-exact-finite-models
  - literal-mark-quotient-via-exact-finite-models
distinct_from:
  finite-quotient-blindness: That claim says the compression data dies in a finite quotient; this one runs the same collapse on a local embedding and concludes non-LEF for the two marked quotients, where the defect is still nontrivial.
  cyclic-base-sharpness: That is the (T)-free calibration whose quotient is amenable and MF; this claim is the affine-base statement, where amenability is unavailable.
artifacts:
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
  - GroupApproximation/Criterion/FiniteQuotientBlindness.lean
  - GroupApproximation/Monsters/CyclicBaseLEFObstruction.lean
---

None of `E`, `W`, `E/<w>`, `W/<zeta>` is locally embeddable into finite
groups; in particular none is residually finite.  Any group in which the six
compression relations `tau s tau^{-1} = abar(s)`, the centralizer relations
`[c,s] = 1`, and `u = [tau c tau^{-1}, s_1] != 1` all hold fails LEF.

Consequently every MF route for the two marked quotients that factors through
residual finiteness, local finiteness, or local embeddability into finite
groups is closed.  It also settles the residual-finiteness disjunct of
`literal-mark-quotient-flexibly-stable`: `E/<w>` is not residually finite, so
the Gohla--Thom disjunction there is satisfied without constraining
permutation stability.
