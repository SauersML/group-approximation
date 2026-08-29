import GroupApproximation.Sofic.KazhdanCornerMatrices

/-!
# Finite-stage quantitative estimates for the robust spectral gap

`non_mf_group_notes.tex` used to prove the Kazhdan transport result a second
time, in a section titled "The finite-stage transport proof",
"quantitatively at each single coordinate `n` and with no
ultrafilter", with a remark ("The ultrafilter gives no
rate") recording that the error bookkeeping there is explicit in terms of the
Kazhdan constant `κ`, the size `|S|` of the averaging set, the uniform bound
`M` on the transported vectors, and the multiplicative defects of the
microstates, *once the robust spectral-gap input stated there is granted at
each stage*.

**Neither the section nor the remark is printed any more.**  Commit `3a45fa60`
("Editorial pass: rewrite orbit collapse, cut what nothing uses") deleted both,
after the rewritten collapse step stopped consuming the finite-stage route.
What the manuscript prints is the single ultraproduct proof inside
the former transport argument.  Nothing in this file depended on that text, and nothing
in it changed; it is now a Lean-side second route with no printed counterpart
and no badge owed.

This file supplies that explicit bookkeeping.  Every estimate below lives at
one fixed coordinate `n`, is an inequality between real numbers with named
constants, and every proof is finite-dimensional inner-product algebra.  No
ultrafilter, no hyperreal standard part, no compactness extraction and no
sequential limit occurs anywhere in the dependency chain of this module: its
only project import is `GroupApproximation.Sofic.KazhdanCornerMatrices`, whose
transitive import closure contains no hyperreals.

**Operator norm, not Hilbert--Schmidt.**  Section
`\section{Limitations of the operator-norm method}` (`\ref{sec:limits}`)
insists that transport needs operator-norm control -- "Operator-norm control is
needed here to ensure that the classes `[Ad U_n(g)]_ω` are multiplicative;
Hilbert--Schmidt control alone does not provide this" -- and the spectral
estimates below need it for the same reason: `Ad` is not Hilbert--Schmidt
continuous.  That
hypothesis is live in every estimate below.  All operator hypotheses and
conclusions here -- the residual `‖(H - 1) P‖ ≤ δ`, the displacement
`‖(U(g) - 1) P‖`, the leakage `‖(1 - P) Q‖`, and every multiplicative defect
summed by `wordDefect` -- are in the matrix `ℓ²` operator norm of the scoped
instance `Matrix.Norms.L2Operator`, which is the operator norm on the model
Hilbert space; the only Hilbert--Schmidt quantities are the *vectors*
(`‖ξ‖ ≤ M`, `‖(1 - P) ξ‖ ≤ √q`), exactly as in the manuscript's display, since
in the intended instance the model of the almost representation is the adjoint
one and its vectors are the Hilbert--Schmidt vectors `ξ_n` of `x_n`.  Nothing
below is derivable from a Hilbert--Schmidt bound on the microstate defects.

## What is proved here, in the order the appendix uses it

* `sum_norm_act_sub_sq` — the exact energy identity
  `∑_{s ∈ S} ‖U(s)x - x‖² = 2|S| (‖x‖² - ⟪x, H x⟫)`, where `H` is the
  Hermitian average of the microstates over `S` (TeX 1858-1861: "`1 - H_n` is
  the average of the positive operators `1 - Re Ad U_n(ι(s'))`").
* `norm_act_sub_mul_projection_le` — if the residual of `H` on an orthogonal
  projection `P` is at most `δ` in operator norm, then every `s ∈ S` moves
  `ran P` by at most `√(2|S|δ)`.  This is the appendix's
  `½‖(Ad U_n(ι(s')) - 1)η‖² ≤ |S|δ` (TeX 1861) with the constant printed
  and with `P` arbitrary.
* `norm_word_displacement_le` — a word of length `ℓ` in `S` moves `ran P` by
  at most `ℓ√(2|S|δ)` plus the accumulated multiplicative defects along the
  word (`wordDefect`).  This is TeX 1862 verbatim.
* `norm_act_sub_lt_of_eigenvalue_above_gap` — the "too fixed to be moved by
  `κ`" half of the appendix's dichotomy (TeX 1852-1854): a unit eigenvector of
  `H` with eigenvalue above `1 - κ²/(4|S|)` is moved by every `s ∈ S` by
  strictly less than `κ`, at a single coordinate, with no limit.
* `norm_transport_displacement_le`, `transport_bound_sq_le` and
  `transport_bound_le_epsilon` — the appendix's closing computation (TeX
  1903-1936): the three-term decomposition of `T_nξ_n` along `P_n` and `Q_n`,
  and the resulting bound `(qM + 2qM + 2q^{1/2})² ≤ 18q²M² + 16q ≤ ε`.

## What is not proved here

The appendix's robust spectral gap itself — "once the multiplicative defects
of `U_n` on `S` are small enough, no eigenvalue of `H_n` lies in `[a,b]`"
(TeX 1849-1851) — is *not* proved here, and cannot be proved by the
finite-dimensional means of this file.  That statement is about an almost
representation, while Kazhdan's property `(T)` is a statement about exact
unitary representations; the only bridge from one to the other that does not
go through a sum-of-squares certificate for `(T)` is a limit.  The corpus
proves it in `GroupApproximation/Sofic/WeakMFVectorGNS.lean`
(`hermitianAverage_eventually_no_intermediate_eigenvalues`) through a
hyperreal standard part, i.e. through an ultrafilter, and that non-effective
`∃ N` is the only non-explicit input to the estimates below.  For an exact
orthogonal representation the same gap is already proved with no limits at all
by `GroupApproximation.KazhdanEigenvalueBound.eigenvalue_le_of_ne_one`.
-/

/-! ## Matrices acting on Euclidean space -/

/-! ## Real and complex matrix coefficients -/

/-! ## The finite-stage averaging identity

TeX 1839-1843 and 1858-1862: `H_n` is the Hermitian part of the average
of the microstates over `S`, and `1 - H_n` is the average of the positive
operators `1 - Re Ad U_n(ι(s'))`.  The next three lemmas are that sentence,
as an identity of real numbers at a fixed coordinate. -/

/-! ## The displacement identity and the per-generator estimate -/

/-! ## The appendix's estimate (i): displacement of a spectral corner

TeX 1847-1864.  Granted the residual bound `‖(H_n - 1)P_n‖ ≤ δ`, every
generator moves the corner by at most `√(2|S|δ)` in operator norm, with the
constant printed by the manuscript. -/

/-! ## Words: TeX 1862

"a word in `S` of length `ℓ` moves `η` by at most `ℓ√(2|S|δ)` plus the
accumulated multiplicative defects". -/

/-! ## The dichotomy of TeX 1852-1854, finite-stage half

"an eigenvector with intermediate eigenvalue would be a unit vector that the
Kazhdan pair forbids: too fixed to be moved by `κ`, too moved to be fixed."
The first half is an unconditional estimate at a single coordinate and is
proved here.  The second half is a statement about exact representations; see
`GroupApproximation.KazhdanEigenvalueBound.eigenvalue_le_of_ne_one`. -/

/-! ## The appendix's closing computation, TeX 1903-1936 -/
