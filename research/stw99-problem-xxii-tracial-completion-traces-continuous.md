---
rg: 2
id: stw99-problem-xxii-tracial-completion-traces-continuous
kind: claim
title: All traces on a factorial tracially complete C*-algebra are uniform-2-norm continuous (STW Problem XXII)
root: true
distinct_from:
  stw99-problem-x2-hyperfinite-factor-quasidiagonal: that asks for operator-norm matrix models of the single tracial von Neumann algebra R; this asks whether the designated trace simplex of a factorial tracially complete C*-algebra already exhausts all its traces, a normality question with no matrix models involved.
  trace-problem-holds-over-convergent-sequence-boundaries: that is the established special case of this problem for W*-bundles over convergent-sequence spaces; this is the general problem, open even for Bauer simplices with boundary an interval.
artifacts:
  - research/artifacts/stw99-xxii-trace-problem-2026-08-30.md
  - research/artifacts/stw22-uncountable-cofinite-bundle-audit-2026-08-30.md
  - research/artifacts/stw22-intrinsic-zero-dimensional-selection-audit-2026-08-30.md
  - research/artifacts/stw-operator-literature-exact-imports-2026-08-30.md
---

**Problem XXII of Schafhauser--Tikuisis--White, arXiv:2506.10902**
(= Question 1.1 of Carrión--Castillejos--Evington--Gabe--Schafhauser--Tikuisis--White,
*Tracially complete C\*-algebras*, arXiv:2310.20594, the "trace problem").
Let `(M, X)` be a factorial tracially complete C\*-algebra.  Are all tracial
states on `M` automatically `‖·‖_{2,X}`-continuous — equivalently, is
`X ⊆ T(M)` an equality?

Known (CCEGSTW): yes when `X` is a finite-dimensional simplex (`M` is then a
finite direct sum of factors and traces are normal); yes for uniform tracial
ultrapowers and reduced products of tracially complete C\*-algebras with
property Γ (their Theorem 7.5, where CPoU supplies the projections that the
non-von-Neumann fibres lack).

Fu, arXiv:2605.21655v1, Theorem 10.12, also gives the full trace equality for
the completion of an algebraically simple separable non-elementary
stable-rank-one algebra with nonempty compact trace space and locally finite
nuclear dimension.  This is the exact positive class
`fu-locally-finite-nucdim-completions-have-only-uniform-traces`.  It imposes
regularity on a dense C-star algebra rather than a covering-dimension
condition on the bundle base, and it leaves the arbitrary factorial trace
problem open.

New here: yes, with no property Γ hypothesis, for W\*-bundles whose base is
a countable compact space with finitely many limit points
(`trace-problem-holds-over-convergent-sequence-boundaries`).
The countability and metrizability restrictions are removed by
`stw22-finite-derived-set-factor-bundles-have-uniform-traces`: the same
conclusion holds over every compact Hausdorff base with finite derived set,
including one-point compactifications of discrete sets of arbitrary
cardinality.

The finite-derived-set restriction is now removed completely in covering
dimension zero.  `stw22-zero-dimensional-factor-bundles-have-uniform-traces`
proves the conclusion over every compact zero-dimensional Hausdorff base,
with arbitrary finite-factor fibres and no common ambient factor.  In
particular every compact scattered base and every countable compact base is
covered, as are perfect zero-dimensional bases such as Cantor space.  The
proof intrinsically lifts exact fibre tuples, corrects their weighted
partial-isometry relations in `L^2`, and glues them along disjoint clopen
refinements.

For locally trivial hyperfinite W\*-bundles over a finite-dimensional
compact metrizable base,
`stw22-locally-trivial-finite-dimensional-bundles` supplies an independent
chartwise proof of the same trace conclusion.  It is not a new class:
Evington--Pennig, arXiv:1601.05964, prove that every locally trivial
W\*-bundle with all fibres `R` is globally trivial, in every base
dimension.  The chartwise argument is retained as cocycle-local proof
technology.

For arbitrary factorial bundles over finite-dimensional compact metrizable
bases, `stw22-intrinsic-local-replication-colouring-reduction` removes all
global-corner and local-triviality assumptions from the colouring step.  Its
only hypothesis is an exact continuous local tuple of orthogonal weighted
copies.  The existing intrinsic correction lemma makes the corresponding
fibre solution relation lower semicontinuous, but does not continuously
select its polar-fill corrections on a positive-dimensional neighbourhood.
This bundle-valued local selection is now the exact one-dimensional hinge.

## Attempts

* **Central disintegration (general Bauer case).**  For `X` Bauer, `M` is a
  W\*-bundle over `K = ∂_e X` (Ozawa) with centre `C(K)`.  A trace `φ`
  restricts to `μ ∈ Prob(K)` and disintegrates as `φ = ∫ φ_x dμ` with
  `φ_x(fa) = f(x)φ_x(a)`.  `φ_x` kills the ideal
  `J_x = {a : ‖a(y)‖ → 0 at x}`, and the fibre is `M/I_x` with
  `I_x = {a : ‖a(x)‖_{2,x} = 0} ⊇ J_x`; the whole problem is whether
  `φ_x(I_x) = 0`, since traces on the factor fibre are unique.  So the trace
  problem for Bauer boundaries is exactly: no trace charges the germs at `x`
  of sections that are 2-null at `x` but norm-large nearby.
* **The uniform domination property (D).**  It suffices that positive
  contractions `b` with `sup_y τ_y(b(y)) ≤ ε` have `φ(b) ≤ Cε` for every
  trace.  Every route tried factors through (D), and (D) restated is the
  problem itself.
* **The surviving positive-dimensional gluing problem.**  Support
  projections still jump under uniformly 2-small perturbations
  (`b(z)=b(y')+delta_z q_z` with `tau(q_z)` fixed), so one cannot select the
  spectral cuts themselves.  The zero-dimensional theorem bypasses this:
  it lifts weighted operators, corrects only their high spectral parts,
  and patches them on disjoint clopen sets.  Over a connected or
  positive-dimensional base those clopen patches are unavailable.  Local
  weighted tuples then overlap, and no dimension-independent orthogonal
  gluing estimate is presently known.
* **Ultrafilter attack on the negative side.**  A singular trace on
  `C_σ([0,1], R)` of the form `lim_ω τ(b(y_n) q_n)/τ(q_n)` needs projections
  `q_n` with `τ(q_n) → 0` that are asymptotically central in relative
  1-norm against the values of *all* sections; the required rate
  `‖b(y_n) − b(x)‖_2 = o(τ(q_n)^{1/2})` fails for sections built from the
  chosen `q_n` themselves.  No counterexample results, but the failure is
  quantitative, not structural.
