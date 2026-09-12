import GroupApproximation.Computability.ExactLiteralEFinInfSwitch
import GroupApproximation.Sofic.LiteralNonMFEndpoint
import GroupApproximation.Sofic.NormMFConsequences

/-!
# The fixed marked query on the exact event-ray switch

This file connects the algebraic `E/1` switch to the already proved non-MF
mark.  There is no finite-presentation compiler here: the target is the
literal countable presentation from `ExactLiteralEFinInfSwitch`.

The conclusion is exact.  Unbounded events make every homomorphism kill the
mark, while a last event leaves a canonical copy of the literal non-MF group
on which the mark survives.  Moreover, survival itself certifies that the
target is not weak MF, by functoriality of `NormMFInvisible`.
-/

namespace GroupApproximation
namespace ExactLiteralSwitchQuery

open LiteralNonMFPresentation
open LiteralNonMFEndpoint
open ExactLiteralEFinInfSwitch

noncomputable section

/-- The fixed marked homomorphism query on an arbitrary target group. -/
def Survives (G : Type*) [Group G] : Prop :=
  ∃ f : MarkedGroup →* G, f mark ≠ 1

/-- Every homomorphism from the fixed source kills its distinguished mark. -/
def Kills (G : Type*) [Group G] : Prop :=
  ∀ f : MarkedGroup →* G, f mark = 1

theorem survives_iff_not_kills (G : Type*) [Group G] :
    Survives G ↔ ¬ Kills G := by
  simp only [Survives, Kills, not_forall]

/-- A trivial target kills the fixed mark under every homomorphism. -/
theorem kills_of_subsingleton (G : Type*) [Group G] [Subsingleton G] :
    Kills G := by
  intro f
  exact Subsingleton.elim _ _

/-- The infinite-event branch satisfies the universal killing query. -/
theorem kills_of_infiniteEvents (E : StageEvents) (hE : InfiniteEvents E) :
    Kills (SwitchGroup E) := by
  letI : Subsingleton (SwitchGroup E) := subsingleton_of_infiniteEvents E hE
  exact kills_of_subsingleton (SwitchGroup E)

/-- The finite-event branch has an explicit homomorphism on which the mark
survives. -/
theorem survives_of_finiteEvents (E : StageEvents) (hE : FiniteEvents E) :
    Survives (SwitchGroup E) := by
  obtain ⟨e⟩ := nonempty_equiv_literal_of_finiteEvents E hE
  refine ⟨e.symm.toMonoidHom, ?_⟩
  intro h
  apply LiteralNonMFLinearWitness.literal_mark_ne_one
  apply e.symm.injective
  simpa using h

/-- Any target on which the fixed MF-invisible mark survives is non-MF. -/
theorem not_isWeakMF_of_survives {G : Type*} [Group G] [Countable G]
    (h : Survives G) : ¬ IsWeakMF G := by
  obtain ⟨f, hf⟩ := h
  exact not_isWeakMF_of_map_ne_one literal_mark_normMFInvisible f hf

/-- In particular, the surviving branch of the exact switch is non-MF. -/
theorem not_isWeakMF_of_finiteEvents (E : StageEvents) (hE : FiniteEvents E) :
    ¬ IsWeakMF (SwitchGroup E) :=
  not_isWeakMF_of_survives (survives_of_finiteEvents E hE)

/-- The exact, unconditional switch truth table. -/
theorem query_dichotomy (E : StageEvents) :
    (InfiniteEvents E → Kills (SwitchGroup E)) ∧
      (FiniteEvents E →
        Survives (SwitchGroup E) ∧ ¬ IsWeakMF (SwitchGroup E)) := by
  exact ⟨kills_of_infiniteEvents E, fun hE ↦
    ⟨survives_of_finiteEvents E hE, not_isWeakMF_of_finiteEvents E hE⟩⟩

end

end ExactLiteralSwitchQuery
end GroupApproximation
