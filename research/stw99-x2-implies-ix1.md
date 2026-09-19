---
rg: 2
id: stw99-x2-implies-ix1
kind: route
title: Quasidiagonality of the hyperfinite trace restricts through injective GNS closures
target: stw99-problem-ix1-nuclear-faithful-trace-quasidiagonal
requires: [stw99-problem-x2-hyperfinite-factor-quasidiagonal]
artifacts:
  - research/artifacts/stw10-x1-refutation-hostile-audit-2026-08-30.md
---

Assume Problem X(2): the trace of the hyperfinite II₁ factor `R` is
quasidiagonal.  Let `A` be separable nuclear with a faithful trace
`τ`.

1. Nuclearity makes the GNS von Neumann algebra
   `N = π_τ(A)''` injective (every representation of a nuclear
   algebra generates an injective von Neumann algebra); `N` is finite
   with separable predual, hence hyperfinite (Connes) and embeds
   trace-preservingly into `R`.  Composing,
   `ι : A → R` with `τ = τ_R ∘ ι`.
2. Quasidiagonality of `τ_R` restricts along any trace-compatible
   inclusion: the norm-multiplicative u.c.p. models of `R` restrict to
   `ι(A)` with traces converging to `τ`.  So `τ` is a quasidiagonal
   trace on `A`.
3. A FAITHFUL quasidiagonal trace makes the algebra quasidiagonal:
   the models `φ_n` assemble into a *-homomorphism
   `A → ∏_ω M_{k_n}` which is injective because
   `‖φ_n(x)‖ ≥ ‖φ_n(x)‖_{2,tr} → ‖x‖_{2,τ} > 0` for `x ≠ 0`, and it
   comes with its own u.c.p. lift `(φ_n)` — Blackadar--Kirchberg's
   characterisation of quasidiagonality for the represented algebra.

With Problem X(1) now REFUTED (the literal-group counterexample), its
old route to IX(1) is dead; this route makes X(2) the live ancestor of
the nuclear faithful-trace quasidiagonality problem, matching STW's
expectation that X(2) is the heart of the matter.  Note the
counterexample to X(1) does not touch this route: `C*(E)` is
non-nuclear and its trace has NON-injective GNS closure, so it never
enters step 1.
