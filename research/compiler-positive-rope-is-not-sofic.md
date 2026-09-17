---
rg: 2
id: compiler-positive-rope-is-not-sofic
kind: claim
title: Some positive-branch rope R_e of the finite-presentation compiler is not sofic
distinct_from:
  sofic-safe-finite-presentation-compiler: that asks for some compiler whose positive branch is sofic; this asks that the specific rope R_e be nonsofic, which would rule out that route for this compiler and give a locally indicable witness.
  twisted-rope-sofic-once-first-rope-sofic: that is the conditional positive statement for the twisted edge; this is the negative statement for the whole rope.
  the-mikhailova-rope-object-card: that records the object; this is the open negative cell for it.
---

**OPEN.**  For some `e in INF`, the finitely presented group

```text
R_e = < Gamma_e x H, u | u(s,1)u^-1 = (s, tau_e(s)), s in S_e >
```

of [[mf-safe-finite-presentation-compiler]] is not sofic.

**Status of both directions.**
- *If true:* by [[compiler-rope-is-locally-indicable]], `R_e` is a finitely presented locally indicable nonsofic
  group.  That resolves [[left-orderable-non-sofic-group]] through `left-orderable-non-sofic-via-compiler-rope`.
- *If false for all `e`:* `SOFIC_fp` is `Pi^0_2`-complete
  (`sofic-fp-pi2-complete-or-locally-indicable-nonsofic-group`).

So the claim is logically equivalent to the failure of the positive branch of the sofic Rice hypothesis (C1) for
this compiler.

**Constraints on any proof.**
- `R_e` has no infinite property (T) subgroup, so the Kun--Thom rigid-defect mechanism is unavailable.
- `R_e` is locally indicable, so it contains no nontrivial Kazhdan subgroup at all.
- `R_e` is operator-MF on `INF` (the compiler's theorem).  Any obstruction must therefore be invisible to
  operator-norm almost representations.

So a proof would also give an MF nonsofic group.  Hyperlinearity of `R_e` is itself open
([[mf-compiler-positive-branch-is-hyperlinear]]).  If `R_e` were hyperlinear, a proof would have to separate
soficity from hyperlinearity, which is a further open problem.
