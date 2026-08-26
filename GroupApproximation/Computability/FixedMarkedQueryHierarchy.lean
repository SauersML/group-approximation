import GroupApproximation.Computability.ArithmeticalHierarchy
import GroupApproximation.Computability.WordProblemRE

/-!
# The second-level normal form for one fixed marked query

A finite target presentation admits the fixed marked obstruction when there is
one coded image tuple, together with finite certificates for the fixed source
relators, for which no finite derivation kills the marked word.  After packing
the tuple and the relator certificates into one natural number, this has the
normal form `∃ witness, ∀ derivation, check = false`.

This file formalizes that hierarchy layer independently of the group-theoretic
compiler.  The concrete checker is supplied by finite normal-closure proof
verification.  The hardness direction uses Chiodo's torsion-preserving Higman
embedding theorem and remains a cited mathematical input rather than a Lean
declaration.
-/

namespace GroupApproximation
namespace FixedMarkedQueryHierarchy

open ArithmeticalHierarchy

variable {Code : Type} [Primcodable Code]

/-- Effective data for an existential marked query.  The natural number is a
packed image tuple and finite source-relator certificate; the final natural
number is a candidate derivation killing the marked word. -/
structure EffectiveQuery (Code : Type) [Primcodable Code] where
  failureCheck : Code × ℕ → ℕ → Bool
  failureCheck_computable : Computable₂ failureCheck

/-- A target admits the marked query when some certified image tuple survives
every attempted derivation of marked triviality. -/
def Survives (Q : EffectiveQuery Code) (c : Code) : Prop :=
  ∃ witness : ℕ, ∀ derivation : ℕ,
    Q.failureCheck (c, witness) derivation = false

/-- The complementary universal query: every candidate image tuple is either
invalid or has a finite derivation killing the mark. -/
def Kills (Q : EffectiveQuery Code) (c : Code) : Prop :=
  ∀ witness : ℕ, ∃ derivation : ℕ,
    Q.failureCheck (c, witness) derivation = true

theorem kills_iff_not_survives (Q : EffectiveQuery Code) (c : Code) :
    Kills Q c ↔ ¬ Survives Q c := by
  simp only [Kills, Survives]
  push Not
  simp

/-- One universal challenge has an RE answer relation: search for the finite
derivation on which the decidable checker returns true. -/
theorem rePred_answer (Q : EffectiveQuery Code) :
    REPred fun cn : Code × ℕ =>
      ∃ derivation : ℕ, Q.failureCheck cn derivation = true :=
  WordProblemRE.rePred_exists_eq_true Q.failureCheck_computable

/-- The universal fixed-mark query is `Π⁰₂`. -/
theorem kills_pi02 (Q : EffectiveQuery Code) : Pi02 (Kills Q) := by
  refine pi02_of_re_family (rePred_answer Q) ?_
  intro c
  rfl

/-- Equivalently, survival of the fixed marked obstruction is `Σ⁰₂`. -/
theorem survives_sigma02 (Q : EffectiveQuery Code) : Sigma02 (Survives Q) := by
  unfold Sigma02
  exact (pi02_congr fun c => (kills_iff_not_survives Q c).symm).2 (kills_pi02 Q)

/-- A computable reduction into the fixed query, packaged without choosing a
particular source-completeness library. -/
structure Reduction (Source : Type) [Primcodable Source]
    (source : Source → Prop) (Q : EffectiveQuery Code) where
  transform : Source → Code
  transform_computable : Computable transform
  correct : ∀ s, Survives Q (transform s) ↔ source s

theorem Reduction.correct_kills {Source : Type} [Primcodable Source]
    {source : Source → Prop} {Q : EffectiveQuery Code}
    (R : Reduction Source source Q) (s : Source) :
    Kills Q (R.transform s) ↔ ¬ source s := by
  rw [kills_iff_not_survives, not_congr (R.correct s)]

end FixedMarkedQueryHierarchy
end GroupApproximation
