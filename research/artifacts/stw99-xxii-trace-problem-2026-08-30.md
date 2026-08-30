---
title: STW Problem XXII --- the trace problem for tracially complete C*-algebras (2026-08-30)
---

Problem XXII of arXiv:2506.10902 = Question 1.1 of CCEGSTW,
arXiv:2310.20594: for a factorial tracially complete `(M, X)`, is every
trace on `M` uniform-2-norm continuous?

## What is proved here

**Theorem (convergent-sequence boundaries, no property Γ).**  Let `K` be a
countable compact metric space with finitely many limit points and `M` a
W\*-bundle over `K` with finite-factor fibres.  Then `T(M) = X`.

Proof sketch (full detail in
`trace-problem-convergent-sequence-boundaries-proof`): reduce by clopen
separation to `K = ω + 1`; disintegrate over the atomic central measure; at
isolated points traces factor through the fibre factor and are the fibre
trace by the Dixmier property; the residual trace `ψ` at `∞` kills every
finite stage, and for `b` with `b(∞) = 0` the spectral cut
`e_n = 1_{[η,1]}(b(z_n))` has `τ(e_n) → 0`, so both `e` and the `m`
orthogonal partial-isometry copies `v_{i,n}` of `e_n` (per-coordinate
choices, free at isolated points) are sections *because their 2-norms
vanish at `∞`*; then `mψ(e) ≤ 1` for all `m`.  The fibres being von Neumann
factors is what supplies `e_n` and `v_{i,n}`; this is exactly what CPoU
substitutes for in CCEGSTW's Theorem 7.5 for ultrapowers, whose fibres are
not von Neumann algebras.  Neither result contains the other.

## Where the general Bauer case sticks

Everything reduces to the disintegrated germ statement: `φ_x` kills
`I_x = {a : ‖a(x)‖_{2,x} = 0}`.  Equivalently the uniform domination
property (D): traces are uniformly small on positive contractions with
uniformly small fibre traces.  Three structural facts frame it:

1. **Support jumping.**  `b(z) = b(y') + δ_z q_z` with `δ_z → 0` and
   `τ(q_z) = ε/2` fixed is 2-continuous at `y'`, but any family of sections
   dominating the supports `supp b(z)` must jump by 2-mass `ε/2` at `y'`.
   So the covering-sections approach fails at any base with a limit point
   of limit points (Cantor--Bendixson rank ≥ 2), and the spectral cut
   `y ↦ 1_{[η,1]}(b(y))` is not a section there.
2. **Clopen tail factorisation.**  At a rank-2 point `x` with derived
   decomposition `V \ {x} = ⊔_n W_n` (clopen, rank ≤ 1), `φ_x` kills every
   `W_n` outright and factors through
   `∏_n M(W_n) / ⊕_n M(W_n)`; per-block choices are then free *across*
   blocks but must still be sections *within* each block, and the recursion
   reproduces the same problem one rank down with no gain.
3. **No cheap counterexample.**  A singular trace of the form
   `lim_ω τ(b(y_n) q_n)/τ(q_n)` on `C_σ([0,1], R)` requires
   `‖[q_n, b(y_n)]‖_1 = o(τ(q_n))` against *all* sections; sections
   manufactured from the `q_n` themselves (bump-sums `Σ f_n q_n`, which are
   2-continuous precisely because `τ(q_n) → 0`) violate the required rate
   unless the state is 2-continuous after all.  The obstruction to a
   counterexample is quantitative (rates), not structural, so we do not
   record a conjecture either way.

## Sources

* J. Carrión, J. Castillejos, S. Evington, J. Gabe, C. Schafhauser,
  A. Tikuisis, S. White, Tracially complete C\*-algebras,
  arXiv:2310.20594: Question 1.1, Proposition 3.15, Theorem 7.5.
* N. Ozawa, Dixmier approximation and symmetric amenability for
  C\*-algebras, J. Math. Sci. Univ. Tokyo 20 (2013); and
  [96] of CCEGSTW for W\*-bundles.
* J. Dixmier, Les anneaux d'opérateurs de classe finie (Dixmier property).
