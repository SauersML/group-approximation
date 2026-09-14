---
rg: 2
id: deligne-triple-cover-group-algebras-are-stably-finite
kind: claim
title: Group algebras of Deligne's triple cover of Sp4(Z) over fields of positive characteristic are stably finite
refuted_by:
  - deligne-twisted-group-algebra-is-not-stably-finite
distinct_from:
  deligne-triple-cover-ternary-group-algebras-are-stably-finite: that is the established characteristic-three case, through the nilpotent augmentation kernel of the centre; this asks for every positive characteristic, where for p != 3 the centre splits the algebra into two twisted group algebras of Sp4(Z) with a non-inflated multiplier.
  deligne-triple-cover-surjunctive: that asks for surjectivity of every injective automaton over every alphabet; this is only the linear case over finite fields.
artifacts:
  - research/artifacts/deligne-twisted-group-algebras-2026-09-12.md
  - research/artifacts/deligne-triple-cover-surjunctivity-2026-09-12.md
---

**OPEN.** For every field `F` of positive characteristic, `F[E_3]` is stably finite, where `E_3` is Deligne's
triple cover of `Sp_4(Z)`.

**The cases.**
- **Characteristic three:** established (`deligne-triple-cover-ternary-group-algebras-are-stably-finite`).
- **Characteristic `p != 3`:** the claim is exactly stable finiteness of the two twisted group algebras
  `F^(w^(ja))[Sp_4(Z)]`, `j = 1, 2` (w3-deligne artifact, Lemma 4.1). Their multiplier is not inflated from any
  finite quotient.

**Payoff.** `E_3` carries no strict linear automaton over any finite field
(`stable-finiteness-failure-refutes-surjunctivity`, contrapositive).

## Attempts

- **Rank projective models:** open, and sufficient
  (`deligne-cover-stable-finiteness-from-rank-projective-models`).
- **Traces:** no help in positive characteristic. The HS and C-star trace results on the Deligne fibres say
  nothing about direct finiteness over finite fields.
- **Finite-dimensional or locally finite models: dead.** The twisted algebras have no nonzero
  finite-dimensional module (artifact Lemma 1.1).
- **Virtually split supports:** harmless. A witness pair supported on a subgroup over which the multiplier
  dies on a finite-index subgroup lives in `M_d` of an untwisted group algebra of a linear group, which is
  stably finite. So the support must keep `z` in the finite residual of its preimage, as in
  `strict-automata-memory-keeps-finite-normal-kernel-residual`.
