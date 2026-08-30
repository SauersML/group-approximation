---
rg: 2
id: stw99-problem-xxii-tracial-completion-traces-continuous
kind: claim
title: All traces on a factorial tracially complete C*-algebra are uniform-2-norm continuous (STW Problem XXII)
root: true
distinct_from:
  stw99-problem-x2-hyperfinite-factor-quasidiagonal: that asks for operator-norm matrix models of the single tracial von Neumann algebra R; this asks whether the designated trace simplex of a factorial tracially complete C*-algebra already exhausts all its traces, a normality question with no matrix models involved.
  stw22-dim1-factor-bundles-have-uniform-traces: that proves the problem for countably generated factorial bundles over bases of dimension at most one; this is the unrestricted problem, with neither a dimension nor countable-generation hypothesis.
artifacts:
  - research/artifacts/stw99-xxii-trace-problem-2026-08-30.md
  - research/artifacts/stw22-uncountable-cofinite-bundle-audit-2026-08-30.md
  - research/artifacts/stw22-intrinsic-zero-dimensional-selection-audit-2026-08-30.md
  - research/artifacts/stw22-stabilized-l2-selection-audit-2026-08-30.md
  - research/artifacts/stw22-arbitrary-factor-stiefel-boundary-audit-2026-08-30.md
  - research/artifacts/stw22-matrix-weighted-loop-filling-audit-2026-08-30.md
  - research/artifacts/stw22-dim2-arbitrary-factor-breakthrough-2026-08-30.md
  - research/artifacts/stw22-diffuse-spectral-capture-audit-2026-08-30.md
  - research/artifacts/stw22-diffuse-weighted-loop-extension-audit-2026-08-30.md
  - research/artifacts/stw22-fixed-factor-s2-filling-audit-2026-08-30.md
  - research/artifacts/stw22-s2-hard-carrier-obstruction-audit-2026-08-30.md
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

For countably generated factorial bundles, the dimension-zero restriction
is removed through dimension one by
`stw22-dim1-factor-bundles-have-uniform-traces`.  Stabilization embeds the
intrinsic Hilbert `C(K)`-module of `L^2` sections as a complemented submodule
of `C(K,ell^2)`.  This puts all varying factor fibres in one complete metric
space without embedding them in a common factor.  The exact weighted-copy
multifunction is lower semicontinuous and uniformly locally path connected,
so one-dimensional selection gives global copies.  Spectral clipping proves
that the selected fibrewise contractions belong to the original tracially
complete algebra, rather than merely to its Hilbert-module completion.
Countable generation is automatic for uniform completions of separable
C-star algebras.

For trivial bundles, Farah--Vaccaro, Proc. Amer. Math. Soc. 154 (2026),
Theorem 1.2, independently remove countable generation: for every II1 factor
`N` and compact Hausdorff `X` with `dim(X)<=1`, all traces on
`C_sigma(X,N)` are canonical. In particular the interval and circle with
free-group-factor fibre are settled. See
`farah-vaccaro-one-dim-trivial-bundles-uniform-traces`.

The first higher-dimensional trivial case is also closed.
`stw22-dim2-trivial-factor-bundles-have-uniform-traces` proves that every
trace on `C_sigma(X,N)` is canonical for every separable-predual II1
factor `N` and every compact Hausdorff `X` with `dim(X)<=2`.  Its relative
low-spectrum disk extension was the first proof across dimension two; the
countably generated nontrivial-bundle theorem below strictly extends this
conclusion.  Beyond dimension two, arbitrary nontrivial bundles remain open.

The fixed-factor trivial case now reaches dimension three.
`stw22-dim3-trivial-factor-bundles-have-uniform-traces` applies to every
separable-predual `II_1` factor.  Its `S^2` filling modulus may depend on
that fixed factor through a pointed Jekel contraction; obtaining one modulus
simultaneously for varying factor fibres remains open.
The naive multiplicity-three hard-carrier bootstrap is ruled out by
`stw22-hard-carrier-unions-fail-local-connectivity`: infinitesimally split
carriers force a fixed transverse join, breaking local connectivity (or,
with simplex coordinates, lower semicontinuity).

For locally trivial hyperfinite W\*-bundles over a finite-dimensional
compact metrizable base,
`stw22-locally-trivial-finite-dimensional-bundles` supplies an independent
chartwise proof of the same trace conclusion.  It is not a new class:
Evington--Pennig, arXiv:1601.05964, prove that every locally trivial
W\*-bundle with all fibres `R` is globally trivial, in every base
dimension.  The chartwise argument is retained as cocycle-local proof
technology.

For arbitrary factorial bundles over finite-dimensional compact metrizable
bases,
`stw22-intrinsic-local-replication-colouring-reduction` removes all
global-corner and local-triviality assumptions from the colouring step.  Its
only hypothesis is an exact continuous local tuple of orthogonal weighted
copies.  The existing intrinsic correction lemma makes the corresponding
fibre solution relation lower semicontinuous, but does not supply the
uniform higher local connectivity needed to select its polar-fill
corrections.  In the countably generated case the degree-zero selection
problem is settled through dimension two by stabilized `L^2` selection and
the all-factor weighted loop-filling theorem.  For countably generated
bundles, sphere degrees at least two are now the first finite-dimensional
hinge.

For the first such hinge, projection-weight multicopy fibres reduce exactly
to `U(N)/(q+U((1-q)N(1-q)))`.  The complement bound is indispensable:
without it,
determinant loops in `U(n)` have normalized `2`-radius tending to zero but
remain non-null-homotopic. Positive complement slack removes that elementary
obstruction, and `stw22-matrix-weighted-copy-uniform-loop-fillings` now
proves a dimension-free filling-radius estimate for all matrix factors,
positive weights, and replication numbers. The hyperfinite `II_1` case is
already covered by `stw22-strong-stiefel-spaces-have-uniform-loop-fillings`.
The non-hyperfinite projection-weight case is closed by
`stw22-diffuse-stiefel-uniform-loop-fillings`: a summable sequence of
orthogonal norm-continuous carriers produces the missing continuous
small-trace spectral projection.  The relative low-spectrum step is closed
by `stw22-all-finite-factor-weighted-copy-uniform-loop-fillings`: a unitary
lift of the high filling and an explicit band-by-band trivialization of its
moving complement give a universal cubic modulus for arbitrary positive
weights and copy numbers.  Stabilized two-dimensional Michael selection now
proves `stw22-dim2-factor-bundles-have-uniform-traces` for every countably
generated factorial bundle over a base of covering dimension at most two.

The tempting matrix-cone shortcut is strictly stronger than this hinge.
`stw22-bare-cone-projectivity-does-not-supply-ilr` exhibits a
one-dimensional trivial matrix field where global ILR holds and an
unrestricted fibre cone map lifts globally, yet no local lift can preserve
the prescribed `e_00` corner. The relative cone condition forces the source
support to be orthogonal to the replication ranges, a relation absent from
ILR. Ordinary cone projectivity therefore does not settle the selection
problem.

Using `M_m` instead and counting the source as the first range gives an exact
cone formulation of anchored ILR, but its corner-preserving lift is itself
the unresolved relative selection statement.

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
* **The surviving higher-dimensional gluing problem.**  Support
  projections still jump under uniformly 2-small perturbations
  (`b(z)=b(y')+delta_z q_z` with `tau(q_z)` fixed), so one cannot select the
  spectral cuts themselves.  The zero-dimensional theorem bypasses this:
  it lifts weighted operators, corrects only their high spectral parts,
  and patches them on disjoint clopen sets.  Stabilized intrinsic `L^2`
  selection now replaces those patches through dimension two for countably
  generated bundles.  From dimension three onward, local weighted tuples
  require uniform higher-connectivity data, and no general varying-factor
  sphere-filling or dimension-independent orthogonal gluing estimate is
  presently known.
* **Ultrafilter attack on the negative side.**  A singular trace on
  `C_σ([0,1], R)` of the form `lim_ω τ(b(y_n) q_n)/τ(q_n)` needs projections
  `q_n` with `τ(q_n) → 0` that are asymptotically central in relative
  1-norm against the values of *all* sections; the required rate
  `‖b(y_n) − b(x)‖_2 = o(τ(q_n)^{1/2})` fails for sections built from the
  chosen `q_n` themselves.  No counterexample results, but the failure is
  quantitative, not structural.
