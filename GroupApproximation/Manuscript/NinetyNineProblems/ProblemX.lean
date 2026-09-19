import GroupApproximation.Analysis.TikuisisWhiteWinterCore
import GroupApproximation.Analysis.UCPContractiveMatrix
import GroupApproximation.Analysis.ShulmanTraceNorms
import GroupApproximation.Analysis.LocallyRFByIntFactorization
import GroupApproximation.Sofic.LiteralTraceConsequence
import GroupApproximation.Sofic.StableLetterLEFRoute
import GroupApproximation.Sofic.TraceSeparationEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# STW Problem X(1) on the literal group `E`

Schafhauser, Tikuisis and White, *Nuclear C⋆-algebras: 99 problems*,
arXiv:2506.10902, print as Problem X(1):

> Is every amenable trace quasidiagonal?

Both notions are Brown's, from *Invariant means and finite representation
theory of C⋆-algebras*, Mem. Amer. Math. Soc. **184** (2006), no. 865:
amenable traces are the equivalent conditions of his Theorem 3.1.6, and
quasidiagonal traces are Definition 3.3.1.  The repository already carries
both, transcribed clause for clause, as
`Quasidiagonal.AmenableTraceModel` / `Quasidiagonal.IsAmenableTrace` and
`Quasidiagonal.QuasidiagonalTraceModel` /
`Quasidiagonal.IsQuasidiagonalTrace`.  The two structures differ in exactly
one field: the multiplicative defect `φₙ(ab) − φₙ(a)φₙ(b)` is asked to vanish
in the normalized Hilbert--Schmidt norm for an amenable trace and in the
operator norm for a quasidiagonal one.  So the easy half of X(1) is the
inequality `‖x‖₂ ≤ ‖x‖`, and it is proved: it is
`Quasidiagonal.isAmenableTrace_of_isQuasidiagonalTrace`.  Problem X(1) asks
for the converse with no hypothesis on the algebra --- Tikuisis, White and
Winter, Ann. of Math. (2) **185** (2017), 229--284, prove it for a faithful
trace on a separable nuclear algebra satisfying the UCT.

`ProblemX1Statement` below is that converse, at the repository's own two
definitions, universe-polymorphic and with no hypothesis on `A` beyond a
C⋆-algebra structure.

## Where the literal group enters

For a discrete group `G` the canonical trace of the full group C⋆-algebra is
an amenable trace exactly when `G` has Kirchberg's factorization property
(Brown, Theorem 4.1.9).  The repository's literal forty-one-relator group
`E = LiteralNonMFPresentation.MarkedGroup` is finitely presented, sofic and
hyperlinear, and about its canonical trace `τ_E` on `C⋆(E)` two things are
proved here, both unconditionally:

* `τ_E` is a **hyperlinear trace** --- matrix models with all three defects
  small in the normalized Hilbert--Schmidt norm --- because `E` is sofic
  (`literalCanonicalTrace_isHyperlinearTrace`); and
* `τ_E` is **not a quasidiagonal trace**, because a quasidiagonal trace is an
  MF trace and `τ_E` is not one
  (`literalCanonicalTrace_not_isQuasidiagonalTrace`).

Neither half is new analysis.  Both are read off
`LiteralTraceConsequence.markedGroup_canonicalTrace_isHyperlinearTrace_not_isMFTrace`
--- the hyperlinear/MF separation the manuscript already prints --- once
`Quasidiagonal.isMFTrace_of_isQuasidiagonalTrace` is applied to move from the
MF class to the quasidiagonal one.

The additional structure of `E` closes the amenability clause.  The printed
stable-letter decomposition gives `E ≃ E₀ ⋊ ℤ`, and every finitely generated
subgroup of `E₀` is residually finite.  For a finite packet of group elements,
a long cyclic integer window and one finite quotient of the finitely generated
normal-coordinate subgroup give a finite family of cosets.  Compressing the
corresponding quasi-regular representation gives genuinely u.c.p. maps.
Residual separation makes their generator traces exact, while only the ends
of the integer window contribute to the Hilbert--Schmidt multiplicative
defect.  The boundary ratio tends to zero, and density extends the estimates
to the full group C⋆-algebra.

`LocallyRFByIntFactorization.canonicalMaximalTrace_isAmenableTrace_of_locallyRFByInt`
formalizes that construction.  Applying it to the stable-letter decomposition
proves `literalFactorizationProperty`; combining this with the failure of
quasidiagonality gives the unconditional negative answer
`not_problemX1Statement`.
-/

open Filter Matrix
open scoped Matrix.Norms.L2Operator

namespace GroupApproximation
namespace NinetyNineProblems

open LiteralNonMFPresentation

noncomputable section

universe u

/-! ## The problem, as a proposition -/

/-- **Problem X(1) of Schafhauser--Tikuisis--White**, arXiv:2506.10902: is
every amenable trace on a C⋆-algebra quasidiagonal?

Stated at the repository's transcriptions of Brown's two definitions
(Mem. AMS **184** (2006), Theorem 3.1.6 and Definition 3.3.1), with the trace
a bundled `TracialState` --- the word "trace" in both definitions presupposes
an actual tracial state, and `IsAmenableTrace` / `IsQuasidiagonalTrace` carry
only the approximation clauses.

The converse implication is unconditional and already proved, as
`Quasidiagonal.isAmenableTrace_of_isQuasidiagonalTrace`, so this proposition
is exactly the open half of an equivalence. -/
def ProblemX1Statement : Prop :=
  ∀ (A : Type u) [CStarAlgebra A] (τ : TracialState A),
    Quasidiagonal.IsAmenableTrace (fun a : A ↦ τ a) →
      Quasidiagonal.IsQuasidiagonalTrace (fun a : A ↦ τ a)

/-! ## An amenable trace is a hyperlinear trace -/

/-- **The u.c.p. models of an amenable trace, read as Hilbert--Schmidt
approximation data.**

Three of the five clauses of `ShulmanTrace.TraceApproximationModel` are free
here: linearity is exact, so its defect is identically `0`;
`⋆`-compatibility is exact by `Quasidiagonal.ucp_map_star`, a unital
completely positive map into a matrix algebra preserving adjoints; and both
defects are then `TracialUltraproduct.hsNorm_zero`.  The boundedness clause is
the operator-norm contractivity of a u.c.p. map, which is
`Quasidiagonal.ucpContractive` --- discharged in
`Analysis/UCPContractiveMatrix.lean`, so it enters as a term and not as a
hypothesis.  The multiplicative and trace clauses are transcribed unchanged.

The direction is the cheap one: amenability of a trace already hands over
u.c.p. maps, and a hyperlinear trace asks for less.  The content of Problem
X(1) sits on the other side. -/
def amenableHilbertSchmidtModel {A : Type u} [CStarAlgebra A] {τ : A → ℂ}
    (M : Quasidiagonal.AmenableTraceModel τ) :
    ShulmanTrace.TraceApproximationModel atTop (fun Y B ↦ hsNorm Y B) τ where
  space := M.space
  map n := ⇑(M.map n)
  tendsto_mul a b := M.tendsto_mul_hs a b
  tendsto_linear c₁ c₂ a b :=
    ShulmanTrace.tendsto_zero_of_eq_zero fun n ↦ by
      simp only [map_add, map_smul, add_sub_cancel_left, sub_self,
        TracialUltraproduct.hsNorm_zero]
  tendsto_star a :=
    ShulmanTrace.tendsto_zero_of_eq_zero fun n ↦ by
      simp only [Quasidiagonal.ucp_map_star (M.map n) (M.map_one n)
        (M.completelyPositive n) a, sub_self, TracialUltraproduct.hsNorm_zero]
  bounded a := ⟨‖a‖, fun n ↦ Quasidiagonal.ucpContractive.norm_le A inferInstance
    (M.space n) (M.map n) (M.map_one n) (M.completelyPositive n) a⟩
  tendsto_trace := M.tendsto_trace

/-- **An amenable trace is a hyperlinear trace.**

The tracial-state datum is separate in both directions --- Brown's amenable
traces are traces by fiat, whereas `Quasidiagonal.IsAmenableTrace` carries
only the approximation clauses, so it is supplied here as `hτ`, exactly as
`Quasidiagonal.isMFTrace_of_isQuasidiagonalTrace` supplies it.

Together with `Quasidiagonal.isAmenableTrace_of_isQuasidiagonalTrace` this
places the three classes in a line: quasidiagonal ⟹ amenable ⟹ hyperlinear.
Problem X(1) asks whether the first arrow reverses.  The second arrow does
not reverse in general --- Thom's LEF Kazhdan groups (arXiv:0810.2180) carry
hyperlinear canonical traces without the factorization property, so without
amenable ones.  The locally-RF-by-integer structure below is the extra input
that proves amenability for the canonical trace of `E`. -/
theorem isHyperlinearTrace_of_isAmenableTrace {A : Type u} [CStarAlgebra A]
    {τ : A → ℂ} (hτ : IsTracialState τ)
    (h : Quasidiagonal.IsAmenableTrace τ) :
    ShulmanTrace.IsHyperlinearTrace τ := by
  obtain ⟨M⟩ := h
  exact ⟨hτ, ⟨amenableHilbertSchmidtModel M⟩⟩

/-! ## The canonical trace of the literal group -/

/-- The canonical trace of `C⋆(E)` is an actual tracial state, in the
predicate form the MF- and hyperlinear-trace classes consume.

The bundle is `ShulmanTrace.canonicalMaximalTracialState`, which already
carries the four facts for every group: linearity from the continuous linear
map itself, and normalization, positivity on `a⋆a` and invariance under
swapping a product from `canonicalMaximalTrace_isTracialState`.  Faithfulness
is neither available nor needed --- the canonical map `C⋆(E) → C⋆_r(E)` has a
kernel, `E` being non-amenable --- and no trace class used below asks for
it. -/
theorem literalCanonicalTrace_isTracialState :
    IsTracialState
      (fun a : MaximalGroupCStar MarkedGroup ↦ canonicalMaximalTrace MarkedGroup a) :=
  ⟨ShulmanTrace.canonicalMaximalTracialState MarkedGroup, fun _ ↦ rfl⟩

/-! ## The two halves, proved -/

/-- **The canonical trace of `C⋆(E)` is a hyperlinear trace.**

This is the first component of
`LiteralTraceConsequence.markedGroup_canonicalTrace_isHyperlinearTrace_not_isMFTrace`,
named here because Problem X(1) is asked about this trace and not about the
MF/hyperlinear separation the endpoint was built for.  Its content is
`ShulmanTrace.canonicalMaximalTrace_isHyperlinearTrace_of_isSofic` at
`LiteralSoficAssembly.markedGroup_isSofic`: for a countable sofic group a
sofic approximation's permutation matrices represent `C⋆(G)` in the `atTop`
tracial matrix quotient, and bounded elementwise representatives of that
representation are the models. -/
theorem literalCanonicalTrace_isHyperlinearTrace :
    ShulmanTrace.IsHyperlinearTrace
      (fun a : MaximalGroupCStar MarkedGroup ↦ canonicalMaximalTrace MarkedGroup a) :=
  LiteralTraceConsequence.markedGroup_canonicalTrace_isHyperlinearTrace_not_isMFTrace.1

/-- **The canonical trace of `C⋆(E)` is not a quasidiagonal trace.**

A quasidiagonal trace is an MF trace: every clause of
`ShulmanTrace.MFTraceModel` is weaker than the corresponding u.c.p. clause,
once contractivity is known, and contractivity is
`Quasidiagonal.ucpContractive`.  The canonical trace of `C⋆(E)` is not an MF
trace --- `LiteralTraceConsequence.markedGroup_canonicalMaximalTrace_not_isMFTrace`,
which is Theorem A read at the trace --- so it is not quasidiagonal.

No hypothesis is consumed: the only input this route used to carry,
`Quasidiagonal.UCPContractive`, was discharged in
`Analysis/UCPContractiveMatrix.lean`. -/
theorem literalCanonicalTrace_not_isQuasidiagonalTrace :
    ¬ Quasidiagonal.IsQuasidiagonalTrace
      (fun a : MaximalGroupCStar MarkedGroup ↦ canonicalMaximalTrace MarkedGroup a) := by
  intro h
  exact LiteralTraceConsequence.markedGroup_canonicalMaximalTrace_not_isMFTrace
    (Quasidiagonal.isMFTrace_of_isQuasidiagonalTrace literalCanonicalTrace_isTracialState
      Quasidiagonal.ucpContractive h)

/-- **The separation, as the research graph cites it.**  The canonical trace
of `C⋆(E)` is a hyperlinear trace and is not a quasidiagonal trace.

Unconditional, and strictly weaker than
`LiteralTraceConsequence.markedGroup_canonicalTrace_isHyperlinearTrace_not_isMFTrace`,
which separates the same trace from the *MF* traces: a quasidiagonal trace is
MF, so `¬ IsMFTrace` implies `¬ IsQuasidiagonalTrace`.  The weaker form is
the one Problem X(1) is stated in, and it is what the conjunction is for. -/
theorem literalCanonicalTrace_hyperlinear_not_quasidiagonal :
    ShulmanTrace.IsHyperlinearTrace
        (fun a : MaximalGroupCStar MarkedGroup ↦ canonicalMaximalTrace MarkedGroup a) ∧
      ¬ Quasidiagonal.IsQuasidiagonalTrace
        (fun a : MaximalGroupCStar MarkedGroup ↦ canonicalMaximalTrace MarkedGroup a) :=
  ⟨literalCanonicalTrace_isHyperlinearTrace,
    literalCanonicalTrace_not_isQuasidiagonalTrace⟩

/-! ## The factorization property and the unconditional counterexample -/

/-- **Kirchberg's factorization property for `E`, as a named proposition.**

For a discrete group `G` the canonical trace of `C⋆(G)` is an amenable trace
exactly when `G` has the factorization property (Brown, Mem. AMS **184**
(2006), Theorem 4.1.9), so this proposition *is* the factorization property
for `E`, written where this development can consume it.

It is proved below directly from `E ≃ E₀ ⋊ ℤ` and local residual finiteness of
`E₀`; it is not inferred from soficity. -/
def LiteralFactorizationProperty : Prop :=
  Quasidiagonal.IsAmenableTrace
    (fun a : MaximalGroupCStar MarkedGroup ↦ canonicalMaximalTrace MarkedGroup a)

/-- The canonical maximal trace of the literal group is amenable.  This is the
locally-RF-by-integer finite-window theorem instantiated with the exact
stable-letter decomposition of `E`. -/
theorem literalFactorizationProperty : LiteralFactorizationProperty :=
  LocallyRFByIntFactorization.canonicalMaximalTrace_isAmenableTrace_of_locallyRFByInt
    StableLetterLEFRoute.shiftAction
    StableLetterLEFRoute.markedGroupEquivKernelByInt
    StableLetterLEFRoute.telescopeKernel_locallyResiduallyFinite

/-- **`E` refutes Problem X(1), given the factorization property.**

If the canonical trace of `C⋆(E)` is amenable, then an affirmative answer to
X(1) would make it quasidiagonal, and it is not
(`literalCanonicalTrace_not_isQuasidiagonalTrace`).  The universe is pinned at
`1` because `MarkedGroup : Type` and `MaximalGroupCStar` raises the level by
one, so `C⋆(E) : Type 1`.

The hypothesis is kept explicit because this logical bridge is also useful
independently of the particular construction above. -/
theorem not_problemX1Statement_of_literalFactorizationProperty
    (h : LiteralFactorizationProperty) : ¬ ProblemX1Statement.{1} := by
  intro hX
  have hamen : Quasidiagonal.IsAmenableTrace
      (fun a : MaximalGroupCStar MarkedGroup ↦
        ShulmanTrace.canonicalMaximalTracialState MarkedGroup a) := h
  have hqd : Quasidiagonal.IsQuasidiagonalTrace
      (fun a : MaximalGroupCStar MarkedGroup ↦
        ShulmanTrace.canonicalMaximalTracialState MarkedGroup a) :=
    hX (MaximalGroupCStar MarkedGroup)
      (ShulmanTrace.canonicalMaximalTracialState MarkedGroup) hamen
  exact literalCanonicalTrace_not_isQuasidiagonalTrace hqd

/-- **Unconditional negative solution to Problem X(1).**  The canonical trace
of the full group C⋆-algebra of `E` is amenable but not quasidiagonal. -/
theorem not_problemX1Statement : ¬ ProblemX1Statement.{1} :=
  not_problemX1Statement_of_literalFactorizationProperty
    literalFactorizationProperty

end

end NinetyNineProblems
end GroupApproximation

open GroupApproximation.NinetyNineProblems

#audit_axioms ProblemX1Statement
#audit_axioms LiteralFactorizationProperty
#audit_axioms isHyperlinearTrace_of_isAmenableTrace
#audit_closed_axioms literalCanonicalTrace_isHyperlinearTrace
#audit_closed_axioms literalCanonicalTrace_not_isQuasidiagonalTrace
#audit_closed_axioms literalCanonicalTrace_hyperlinear_not_quasidiagonal
#audit_closed_axioms literalFactorizationProperty
#audit_axioms not_problemX1Statement_of_literalFactorizationProperty
#audit_closed_axioms not_problemX1Statement
