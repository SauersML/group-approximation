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

## Attempts

- **Where a permutation obstruction must live (sw-040, 2026-09-17; reduction, one direction).**
  [[hub-incidence-color-code-makes-edge-coset-action-sofic]] proves that a lamp-free hub incidence
  color code (HC_e) on `K_e` makes `Gamma_e action Gamma_e/S_e` sofic. The proof glues the free lamp
  fibres over the hub using a Hall-separable finite quotient of the lamp palette. With
  [[envelope-coset-action-sofic-once-edge-coset-action-sofic]], soficity of `Gamma_e` together with
  (HC_e) gives soficity of `R_e`. So a nonsoficity proof for `R_e` must refute soficity of `Gamma_e`
  or refute (HC_e). (HC_e) involves only one sofic model of the residually finite group `K_e` and
  three colorings:
  - a coloring exact for `K_e/F`;
  - a coloring exact for `K_e/L_e`;
  - a relation between the two that detects `k in F L_e`.

  The lamps, the hub coupling and the free product structure no longer appear. Necessity of (HC_e)
  is open. It is the natural target for a permutation obstruction invisible to operator norms.
- **What (HC3) sees on the compiler (open frontier).** With `F` embedded as `f -> (f, w_f, 1, f, 1)`
  (`pi w_f = iota q(f)`), the quotient `K_e/L_e` is `H_e x P` through
  `(a, u, u', b, p) L_e -> (pi(u) pi(u')^-1, p jq(b)^-1)`, and `F.x_0` is the twisted diagonal
  `Q' = {(iota q, j(q)^-1) : q in Q_e}`. So `k in F L_e` iff `k.x_0 in Q'`, and (HC3) asks for a
  coloring that decodes membership in `Q'` from a sofic model of `H_e x P`. The naive candidate
  (lamp colour from the free-cover frame of
  [[free-cover-left-right-action-over-sofic-group-is-sofic]], relation "same frame orbit") fails.
  In a sofic model of `H_e`, the orbits of `sigma(iota Q_e)` are large, so they give spurious
  incidences for `k notin F L_e`. The missing input is a relative soficity of the Higman pair
  `(H_e, iota Q_e)` that is compatible with the `P`-coordinate.
- **Trace and l2 obstructions (void).** Invariant random subgroup and trace obstructions on the edge
  vanish, because free sofic models give trivial IRS limits. Strong Atiyah and l2-integrality
  obstructions vanish because `R_e` is locally indicable
  ([[compiler-rope-is-locally-indicable]]).
