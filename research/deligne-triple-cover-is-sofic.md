---
rg: 2
id: deligne-triple-cover-is-sofic
kind: claim
title: Deligne's triple cover of Sp4(Z) is sofic
distinct_from:
  deligne-sector-gap-is-exactly-nonhyperlinearity: that characterizes non-hyperlinearity of the triple cover; soficity implies hyperlinearity, so a non-hyperlinearity proof would refute this claim, while hyperlinearity alone would not prove it.
artifacts:
  - research/artifacts/deligne-triple-cover-surjunctivity-2026-09-12.md
---

**OPEN.** Deligne's connected triple cover `E_3` of `Sp_4(Z)` is sofic.

**What is known.**
- **Sofic radical.** It lies in `Res_fin(E_3) = C_3`, so it is `1` or `C_3`. `E_3` is sofic exactly when some
  homomorphism into a sofic group keeps the central `z` nontrivial, because residually sofic groups are
  sofic.
- **LEF.** `E_3` is finitely presented and not residually finite, so it is not LEF. Any sofic approximation
  must be genuinely approximate on some presentation ball.
- **Payoff.** Soficity makes `E_3` surjunctive (`deligne-triple-cover-surjunctive-from-soficity`).
- **Permanence.** No permanence theorem on main covers finite central extensions whose kernel lies in the
  finite residual. This is the natural test case.

## Attempts

- **Characteristic three.** `k[E_3]` is stably finite for `char k = 3`
  (`deligne-triple-cover-ternary-group-algebras-are-stably-finite`), consistent with soficity. It only
  proves what linear soficity in characteristic three would give.
- **Characteristic p != 3** (lane w4-deligne-twisted, `deligne-twisted-group-algebras-2026-09-12.md`).
  - Soficity would make `E_3` `F_p`-linear sofic (`sofic-implies-linear-sofic-over-every-field`).
  - By `deligne-cover-linear-soficity-is-rank-projective-approximation`, that is exactly rank-approximate
    projective representations of the Deligne multiplier in characteristic `p`.
  - A one-sided pair in a twisted group algebra of `Sp_4(Z)` would therefore refute this claim.
- **Truncating a fixed monomial module: dead.** A sofic approximation obtained by truncating one exact
  monomial twisted module along coordinate Folner sets, such as a twisted induced module, does not exist.
  Property (T) forces a finite orbit, whose line character separates `z` in a finite quotient
  (`deligne-monomial-twisted-modules-have-no-folner-truncations`). Sofic approximations of `E_3`, if they
  exist, must vary intrinsically with the ball.
