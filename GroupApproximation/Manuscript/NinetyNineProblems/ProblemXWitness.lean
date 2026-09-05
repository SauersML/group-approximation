import GroupApproximation.Manuscript.NinetyNineProblems.ProblemX

/-!
# The witness behind the negative answer to Problem X(1), stated positively

`Manuscript/NinetyNineProblems/ProblemX.lean` answers Schafhauser--Tikuisis--White
Problem X(1) --- *is every amenable trace quasidiagonal?* --- in the negative,
as `not_problemX1Statement : ¬ ProblemX1Statement`.  A negated universal is the
shape the printed problem has, and it is the weaker of the two readings: `¬ ∀`
is not `∃ ¬` without excluded middle, and more to the point a reader cannot see
the counterexample in it.

The counterexample is there.  This module names it, in the forms a citation
wants, and audits each one closed:

* `literalCanonicalTrace_isAmenableTrace` --- the amenability half with the
  proposition written out.  `literalFactorizationProperty` proves it already,
  but its advertised type is the *name* `LiteralFactorizationProperty`, so a
  reader has to unfold a definition to see which of Brown's two classes it
  lands in.  Here the class is in the statement.
* `literalCanonicalTrace_amenable_not_quasidiagonal` --- the conjunction.  The
  repository already carries `literalCanonicalTrace_hyperlinear_not_quasidiagonal`,
  which is the same shape one class weaker: *hyperlinear* asks for bounded
  `⋆`-preserving models, and Brown's amenability asks for unital completely
  positive ones.  Problem X(1) is asked at the u.c.p. class, so this is the
  conjunction that answers it, and the two differ by exactly the content of
  `LocallyRFByIntFactorization.canonicalMaximalTrace_isAmenableTrace_of_locallyRFByInt`.
* `AmenableNonQuasidiagonalTrace` and `amenableNonQuasidiagonalTrace` --- the
  existential the problem is asked at.  Brown's question is about C⋆-algebras,
  not about `C⋆(E)`, so a concrete conjunction implies the answer without being
  it; and the algebra is asked to be **separable**, which `C⋆(E)` is, because
  the quasidiagonality literature asks its questions there and an answer at a
  nonseparable algebra would not be one.  Nothing here is a hypothesis: the
  algebra is named, the trace is produced, and every clause is proved.

The shape of the existential, down to the `_inst` binder, is
`ShulmanTrace`-side `Sofic.TraceSeparationEndpoint.SeparableHyperlinearNonMFTrace`,
which answers Shulman's question the same way and for the same reason.

No new mathematics: every proof below is an application of a theorem in
`ProblemX.lean` or of `maximalGroupCStar_separableSpace`.  What is new is that
the class Brown's question is asked at appears in the statements.
-/

namespace GroupApproximation
namespace NinetyNineProblems

open LiteralNonMFPresentation

noncomputable section

universe u

/-- **The canonical trace of `C⋆(E)` is an amenable trace**, with the class
written out rather than hidden behind `LiteralFactorizationProperty`.

Definitionally the same proposition --- `LiteralFactorizationProperty` is
declared as this one --- so the proof is the inhabitant itself. -/
theorem literalCanonicalTrace_isAmenableTrace :
    Quasidiagonal.IsAmenableTrace
      (fun a : MaximalGroupCStar MarkedGroup ↦ canonicalMaximalTrace MarkedGroup a) :=
  literalFactorizationProperty

/-- **The counterexample to Problem X(1).**  The canonical trace of `C⋆(E)` is
an amenable trace and is not a quasidiagonal trace.

Compare `literalCanonicalTrace_hyperlinear_not_quasidiagonal`, whose first
clause is the *hyperlinear* one that soficity of `E` already gives.  Soficity
does not give this one: Thom's LEF Kazhdan groups (arXiv:0810.2180) have
hyperlinear canonical traces and, by Kirchberg's theorem, no factorization
property, so no amenable canonical trace.  The extra input for `E` is its
stable-letter decomposition `E ≃ E₀ ⋊ ℤ` with `E₀` locally residually
finite. -/
theorem literalCanonicalTrace_amenable_not_quasidiagonal :
    Quasidiagonal.IsAmenableTrace
        (fun a : MaximalGroupCStar MarkedGroup ↦ canonicalMaximalTrace MarkedGroup a) ∧
      ¬ Quasidiagonal.IsQuasidiagonalTrace
        (fun a : MaximalGroupCStar MarkedGroup ↦ canonicalMaximalTrace MarkedGroup a) :=
  ⟨literalCanonicalTrace_isAmenableTrace,
    literalCanonicalTrace_not_isQuasidiagonalTrace⟩

/-- The same three facts with the separability of `C⋆(E)` in front, which is
the clause the existential below needs and which `MaximalGroupCStar` has for
every countable group.  Unitality is intrinsic to `MaximalGroupCStar`. -/
theorem literalCanonicalTrace_separable_amenable_not_quasidiagonal :
    TopologicalSpace.SeparableSpace (MaximalGroupCStar MarkedGroup) ∧
      Quasidiagonal.IsAmenableTrace
        (fun a : MaximalGroupCStar MarkedGroup ↦ canonicalMaximalTrace MarkedGroup a) ∧
      ¬ Quasidiagonal.IsQuasidiagonalTrace
        (fun a : MaximalGroupCStar MarkedGroup ↦ canonicalMaximalTrace MarkedGroup a) :=
  ⟨maximalGroupCStar_separableSpace MarkedGroup,
    literalCanonicalTrace_isAmenableTrace,
    literalCanonicalTrace_not_isQuasidiagonalTrace⟩

/-- **The negative answer to Problem X(1), as an existence statement**: some
separable unital C⋆-algebra carries a tracial state that is amenable in Brown's
sense and is not quasidiagonal.

The trace is bundled, so the clause the two approximation classes do not carry
--- that this is an actual tracial state, normalized, positive on `a⋆a`, and
invariant under swapping a product --- is part of the witness rather than an
assumption about it.

Universe-polymorphic, and instantiated at `1` below because that is where
`MaximalGroupCStar` lands; the printed problem names no universe. -/
def AmenableNonQuasidiagonalTrace : Prop :=
  ∃ (A : Type u) (_inst : CStarAlgebra A) (τ : TracialState A),
    TopologicalSpace.SeparableSpace A ∧
      Quasidiagonal.IsAmenableTrace (fun a : A ↦ τ a) ∧
        ¬ Quasidiagonal.IsQuasidiagonalTrace (fun a : A ↦ τ a)

/-- **Problem X(1) fails.**  `C⋆(E)` and its canonical trace discharge
`AmenableNonQuasidiagonalTrace`.

`not_problemX1Statement` is the negation of the printed universal; this is the
existential that produces the counterexample, and it implies that negation
without the classical step. -/
theorem amenableNonQuasidiagonalTrace : AmenableNonQuasidiagonalTrace.{1} :=
  ⟨MaximalGroupCStar MarkedGroup, inferInstance,
    ShulmanTrace.canonicalMaximalTracialState MarkedGroup,
    literalCanonicalTrace_separable_amenable_not_quasidiagonal.1,
    literalCanonicalTrace_separable_amenable_not_quasidiagonal.2.1,
    literalCanonicalTrace_separable_amenable_not_quasidiagonal.2.2⟩

/-- The existential answers the problem: a separable unital C⋆-algebra with an
amenable non-quasidiagonal trace refutes `ProblemX1Statement`, and no excluded
middle is used to get from one to the other.

Recorded as an implication because it is the reading that makes
`amenableNonQuasidiagonalTrace` the stronger statement: `not_problemX1Statement`
follows from it, and not conversely. -/
theorem not_problemX1Statement_of_amenableNonQuasidiagonalTrace
    (h : AmenableNonQuasidiagonalTrace.{1}) : ¬ ProblemX1Statement.{1} := by
  obtain ⟨A, _inst, τ, _, hamen, hqd⟩ := h
  exact fun hX ↦ hqd (hX A τ hamen)

end

end NinetyNineProblems
end GroupApproximation

open GroupApproximation.NinetyNineProblems

#audit_closed_axioms literalCanonicalTrace_isAmenableTrace
#audit_closed_axioms literalCanonicalTrace_amenable_not_quasidiagonal
#audit_closed_axioms literalCanonicalTrace_separable_amenable_not_quasidiagonal
#audit_axioms AmenableNonQuasidiagonalTrace
#audit_closed_axioms amenableNonQuasidiagonalTrace
#audit_axioms not_problemX1Statement_of_amenableNonQuasidiagonalTrace
