import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUniversalDef

/-!
# Shortcut instances for the universal C-star HNN algebra

`universalHNN data` is an `abbrev` for a `StarSubalgebra` of an `lp` indexed by
every covariant representation, so a search for any class *derived* from its
`CStarAlgebra` structure — `Semiring`, `Algebra ℂ`, `DistribMulAction ℂ` — walks
the whole instance graph over that `lp` and exhausts the default typeclass
budget of 20000 heartbeats.

Each instance below is therefore a *projection* of the one above it, never
`inferInstance`: a projection is a one-step hit that matches the head directly,
whereas `inferInstance` would re-run exactly the search we are trying to avoid.
Declared in dependency order so that every step is a field access on an
instance already in scope.  The `Nonempty` side condition of
`universalCStarHNNCStarAlgebra` is discharged by the global
`nonempty_coronaCovariantRepresentation`.

These replace the typeclass budget bumps that previously covered the same
searches: the budget hid the cost, the shortcuts remove it.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- The C-star structure of `U`, stated at the `universalHNN` head so that
downstream searches match in one step. -/
noncomputable instance universalHNNCStarAlgebra
    (data : CoronaConjugator G S T phi A X) :
    CStarAlgebra (universalHNN data) :=
  universalCStarHNNCStarAlgebra (sourceEdgeAlgebra data)
    (targetEdgeAlgebra data) (edgeIsomorphism data)

noncomputable instance universalHNNNormedRing
    (data : CoronaConjugator G S T phi A X) :
    NormedRing (universalHNN data) :=
  (universalHNNCStarAlgebra data).toNormedRing

noncomputable instance universalHNNRing
    (data : CoronaConjugator G S T phi A X) :
    Ring (universalHNN data) :=
  (universalHNNNormedRing data).toRing

noncomputable instance universalHNNSemiring
    (data : CoronaConjugator G S T phi A X) :
    Semiring (universalHNN data) :=
  (universalHNNRing data).toSemiring

noncomputable instance universalHNNStarRing
    (data : CoronaConjugator G S T phi A X) :
    StarRing (universalHNN data) :=
  (universalHNNCStarAlgebra data).toStarRing

noncomputable instance universalHNNNormedAlgebra
    (data : CoronaConjugator G S T phi A X) :
    NormedAlgebra ℂ (universalHNN data) :=
  (universalHNNCStarAlgebra data).toNormedAlgebra

noncomputable instance universalHNNAlgebra
    (data : CoronaConjugator G S T phi A X) :
    Algebra ℂ (universalHNN data) :=
  (universalHNNNormedAlgebra data).toAlgebra

noncomputable instance universalHNNModule
    (data : CoronaConjugator G S T phi A X) :
    Module ℂ (universalHNN data) :=
  Algebra.toModule

noncomputable instance universalHNNDistribMulAction
    (data : CoronaConjugator G S T phi A X) :
    DistribMulAction ℂ (universalHNN data) :=
  Module.toDistribMulAction

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
