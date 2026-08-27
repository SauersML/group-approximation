---
rg: 2
id: kl-coefficient-localization-proof
kind: route
title: Pushout along the coefficient subgroup, then the amalgamated normal form
target: kl-failure-localizes-to-the-coefficient-subgroup
requires: []
artifacts:
  - research/artifacts/kervaire-laudenbach-audit-2026-08-17.md
---

Since `A <= G`, the free product decomposes as

    G * <t>  =  G *_A (A * <t>) ,

and `w` lies in the second factor.  Imposing `w = 1` commutes with the
pushout, so

    G_w  =  G *_A A_w ,

the pushout of `A -> G` and `A -> A_w`.

If `A -> A_w` is injective, both legs are injective and the pushout is an
amalgamated free product `G *_A A_w`; by the normal form theorem for
amalgamated products, both factors embed, in particular `G` does.  That is
the stated implication, and its contrapositive is the localization.

Finite generation of `A` is immediate: a word contains finitely many
coefficients.

`requires: []` is a proof commitment.  Full write-up in
`research/artifacts/kervaire-laudenbach-audit-2026-08-17.md` §C.
