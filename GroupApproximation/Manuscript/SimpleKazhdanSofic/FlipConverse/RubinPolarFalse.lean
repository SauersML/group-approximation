import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RubinPolarRegular
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RubinRegOpenOrder
import GroupApproximation.Meta.AxiomGuard

/-!
# Rubin polars, part 4: the lane's `⇒` half is FALSE

Census row `2e7c7d9ab149`, lane `sk-flip-16`.

## LOUD CORRECTION

The lane target `RigidPolarCharacterizationStatement` says that for Cantor minimal `(X, T)` and
`P ≤ [[T]]`, `IsRigidPolar P ↔ ∃ U clopen, P = F_U`.  **The `⇒` half, and so the whole Statement,
is FALSE.**

* `isRigidPolar_rubinRigidSubgroup_of_regular` (RubinPolarRegular.lean): `F_O` is a rigid polar
  for every regular open `O` (`interior (closure O) = O`).
* `isClopen_of_rigidPolarCharacterization` (below): under the Statement, every regular open
  `O` is clopen.  If `F_O = F_U` then `regOpen_rigid_subset_iff`, applied both ways, gives
  `O = U`.
* Counterexample (on paper): take any Cantor minimal system, e.g. the dyadic odometer, a point
  `x`, and clopen sets `U₀ = X ⊋ U₁ ⊋ U₂ ⊋ ⋯` with `⋂ Uₙ = {x}`.  Let `Rₙ = Uₙ \ Uₙ₊₁`
  (clopen, nonempty) and `O = ⋃ₙ R₂ₙ`.  `O` is open.  Its closure is `O ∪ {x}`, since every
  neighbourhood of `x` contains some `U₂ₙ ⊇ R₂ₙ`, and `x ∉ O`.  Every point other than `x` lies in
  a clopen `Rₘ` that is either inside `O` or disjoint from it.  So `interior (closure O) = O`,
  because `x` is not interior to `O ∪ {x}` (`U₂ₙ₊₁ ⊇ R₂ₙ₊₁` is disjoint from `O ∪ {x}`).  Hence
  `O` is regular open, not closed, and `F_O` is a rigid polar that is not `F_U` for any clopen `U`.

A formal `¬ RigidPolarCharacterizationStatement` needs a concrete Cantor minimal system, which the
corpus does not provide.  The corrected, still unverified, recognition statement used downstream
is `RigidPolarRecognitionStatement` (RubinPolarReduce.lean): rigid polars are of the form `F_O`
with `O` open.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

/-- The literal lane target of `sk-flip-16`.  **FALSE** (see the module docstring): regular open
non-closed sets give counterexamples to `⇒`. -/
def RigidPolarCharacterizationStatement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [PerfectSpace X] [Nonempty X] [TopologicalSpace.MetrizableSpace X] (T : X ≃ₜ X),
    IsMinimalHomeo T → ∀ P : Subgroup (topologicalFullGroup T),
      (IsRigidPolar P ↔
        ∃ U : Set X, IsClopen U ∧ (P : Set (topologicalFullGroup T)) = rigidStabSet T U)

/-- Refutation lemma: the lane Statement forces every regular open set of every Cantor minimal
system to be clopen.  This is false, e.g. for the odometer (module docstring). -/
theorem isClopen_of_rigidPolarCharacterization (h : RigidPolarCharacterizationStatement)
    {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [PerfectSpace X] [Nonempty X] [TopologicalSpace.MetrizableSpace X] {T : X ≃ₜ X}
    (hT : IsMinimalHomeo T) {O : Set X} (hO : IsOpen O) (hreg : interior (closure O) = O) :
    IsClopen O := by
  obtain ⟨U, hU, hPU⟩ := (h X T hT (rubinRigidSubgroup T O)).1
    (isRigidPolar_rubinRigidSubgroup_of_regular hT hO hreg)
  have hsub : ∀ k : topologicalFullGroup T,
      SupportedIn (k : X ≃ₜ X) O ↔ SupportedIn (k : X ≃ₜ X) U := by
    intro k
    have hk : k ∈ (rubinRigidSubgroup T O : Set (topologicalFullGroup T)) ↔
        k ∈ rigidStabSet T U := by
      rw [hPU]
    exact hk
  have h1 : O ⊆ U := (regOpen_rigid_subset_iff hT hO).1 (fun k hk => (hsub k).1 hk)
  have h2 : U ⊆ O := (regOpen_rigid_subset_iff hT hU.isOpen).1 (fun k hk => (hsub k).2 hk)
  have hOU : O = U := Set.Subset.antisymm h1 h2
  rw [hOU]
  exact hU

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RigidPolarCharacterizationStatement
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.isClopen_of_rigidPolarCharacterization
