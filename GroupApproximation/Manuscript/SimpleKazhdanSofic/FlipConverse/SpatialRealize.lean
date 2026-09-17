import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.Converse
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.SpatialInvolutions
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.SpatialStone
import GroupApproximation.Meta.AxiomGuard

/-!
# Spatial realization, part 3: from rigid stabilizers to a spatial isomorphism

Census row `2e7c7d9ab149` (tex: "for topological full groups the converse holds").

`SpatialRealizationStatement` (every `Φ : [[T]] ≃* [[S]]` is `g ↦ h g h⁻¹`) is reduced to the
strictly smaller `RigidStabilizerTransportStatement`: `Φ` maps the rigid stabilizer
`{g | SupportedIn g U}` of each clopen `U ⊆ X` onto the rigid stabilizer of some clopen `V ⊆ Y`.
(It follows from spatial realization with `V = h U`.)  Its remaining content is the purely
group-theoretic recognition of rigid stabilizers of clopen sets inside `[[T]]`.

Reduction (`spatiallyImplemented_of_rigidStabilizerTransport`):
1. Choose `θ U = V`.  By `subset_of_forall_supportedIn` (nontrivial involutions with small
   support), `U ⊆ U' ↔ θ U ⊆ θ U'`; applying the statement to `Φ⁻¹` shows `θ` is onto the clopens.
2. `g⁻¹ ... g` conjugation (`supportedIn_conj_iff`) gives `θ (g⁻¹ U) = (Φ g)⁻¹ (θ U)`.
3. Stone duality (`exists_homeomorph_of_clopen_orderIso`) gives `h` with `h x ∈ θ U ↔ x ∈ U`.
   If `Φ g (h x) ≠ h (g x)`, a clopen `θ U` separates them, but
   `Φ g (h x) ∈ θ U ↔ h x ∈ θ (g⁻¹ U) ↔ g x ∈ U ↔ h (g x) ∈ θ U`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

/-- Isomorphisms of topological full groups of Cantor minimal systems carry rigid stabilizers of
clopen sets to rigid stabilizers of clopen sets. -/
def RigidStabilizerTransportStatement : Prop :=
  ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [PerfectSpace X] [Nonempty X]
    [TopologicalSpace.MetrizableSpace X] [CompactSpace Y] [T2Space Y]
    [TotallyDisconnectedSpace Y] [PerfectSpace Y] [Nonempty Y]
    [TopologicalSpace.MetrizableSpace Y] (T : X ≃ₜ X) (S : Y ≃ₜ Y),
    IsMinimalHomeo T → IsMinimalHomeo S →
      ∀ Φ : topologicalFullGroup T ≃* topologicalFullGroup S, ∀ U : Set X, IsClopen U →
        ∃ V : Set Y, IsClopen V ∧ ∀ g : topologicalFullGroup T,
          (SupportedIn (g : X ≃ₜ X) U ↔
            SupportedIn ((Φ g : topologicalFullGroup S) : Y ≃ₜ Y) V)

theorem spatiallyImplemented_of_rigidStabilizerTransport {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [PerfectSpace X] [CompactSpace Y] [T2Space Y] [TotallyDisconnectedSpace Y] [PerfectSpace Y]
    {T : X ≃ₜ X} {S : Y ≃ₜ Y} (hT : IsMinimalHomeo T) (hS : IsMinimalHomeo S)
    (Φ : topologicalFullGroup T ≃* topologicalFullGroup S)
    (hΦ : ∀ U : Set X, IsClopen U → ∃ V : Set Y, IsClopen V ∧ ∀ g : topologicalFullGroup T,
      (SupportedIn (g : X ≃ₜ X) U ↔ SupportedIn ((Φ g : topologicalFullGroup S) : Y ≃ₜ Y) V))
    (hΦs : ∀ V : Set Y, IsClopen V → ∃ U : Set X, IsClopen U ∧ ∀ k : topologicalFullGroup S,
      (SupportedIn (k : Y ≃ₜ Y) V ↔
        SupportedIn ((Φ.symm k : topologicalFullGroup T) : X ≃ₜ X) U)) :
    ∃ h : X ≃ₜ Y, ∀ (g : topologicalFullGroup T) (x : X),
      ((Φ g : topologicalFullGroup S) : Y ≃ₜ Y) (h x) = h ((g : X ≃ₜ X) x) := by
  have hΦ' : ∀ U : Set X, ∃ V : Set Y, IsClopen U → IsClopen V ∧ ∀ g : topologicalFullGroup T,
      (SupportedIn (g : X ≃ₜ X) U ↔ SupportedIn ((Φ g : topologicalFullGroup S) : Y ≃ₜ Y) V) := by
    intro U
    by_cases hU : IsClopen U
    · obtain ⟨V, hV, hV'⟩ := hΦ U hU
      exact ⟨V, fun _ => ⟨hV, hV'⟩⟩
    · exact ⟨∅, fun h => absurd h hU⟩
  choose θ hθ using hΦ'
  have hθo : ∀ U U' : Set X, IsClopen U → IsClopen U' → (U ⊆ U' ↔ θ U ⊆ θ U') := by
    intro U U' hU hU'
    constructor
    · intro hUU'
      refine subset_of_forall_supportedIn hS (hθ U hU).1.isOpen (hθ U' hU').1.isClosed
        fun k hk hkU => ?_
      have h1 := ((hθ U hU).2 (Φ.symm ⟨k, hk⟩)).2
      have h2 := ((hθ U' hU').2 (Φ.symm ⟨k, hk⟩)).1
      rw [MulEquiv.apply_symm_apply] at h1 h2
      exact h2 ((h1 hkU).mono hUU')
    · intro hθUU'
      refine subset_of_forall_supportedIn hT hU.isOpen hU'.isClosed fun g hg hgU => ?_
      have h1 := ((hθ U hU).2 ⟨g, hg⟩).1 hgU
      exact ((hθ U' hU').2 ⟨g, hg⟩).2 (h1.mono hθUU')
  have hθs : ∀ V : Set Y, IsClopen V → ∃ U : Set X, IsClopen U ∧ θ U = V := by
    intro V hV
    obtain ⟨U, hU, hUV⟩ := hΦs V hV
    refine ⟨U, hU, eq_of_forall_supportedIn_iff hS (hθ U hU).1 hV fun k hk => ?_⟩
    have h1 := (hθ U hU).2 (Φ.symm ⟨k, hk⟩)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1.symm.trans (hUV ⟨k, hk⟩).symm
  have hequiv : ∀ (g : topologicalFullGroup T) (U : Set X), IsClopen U →
      θ ((g : X ≃ₜ X) ⁻¹' U) = ((Φ g : topologicalFullGroup S) : Y ≃ₜ Y) ⁻¹' θ U := by
    intro g U hU
    have hgU : IsClopen ((g : X ≃ₜ X) ⁻¹' U) := hU.preimage (g : X ≃ₜ X).continuous
    have hΦgU : IsClopen (((Φ g : topologicalFullGroup S) : Y ≃ₜ Y) ⁻¹' θ U) :=
      (hθ U hU).1.preimage ((Φ g : topologicalFullGroup S) : Y ≃ₜ Y).continuous
    refine eq_of_forall_supportedIn_iff hS (hθ _ hgU).1 hΦgU fun k hk => ?_
    obtain ⟨m, hm⟩ : ∃ m : topologicalFullGroup T, Φ m = ⟨k, hk⟩ :=
      ⟨Φ.symm ⟨k, hk⟩, MulEquiv.apply_symm_apply Φ _⟩
    have hk' : k = ((Φ m : topologicalFullGroup S) : Y ≃ₜ Y) := congrArg Subtype.val hm.symm
    rw [hk']
    have hconj : Φ (g * m * g⁻¹) = Φ g * Φ m * (Φ g)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    have e1 := ((hθ _ hgU).2 m).symm
    have e2 := (supportedIn_conj_iff (g : X ≃ₜ X) (m : X ≃ₜ X) U).symm
    have e3 := (hθ U hU).2 (g * m * g⁻¹)
    rw [hconj] at e3
    have e4 := supportedIn_conj_iff ((Φ g : topologicalFullGroup S) : Y ≃ₜ Y)
      ((Φ m : topologicalFullGroup S) : Y ≃ₜ Y) (θ U)
    exact e1.trans (e2.trans (e3.trans e4))
  obtain ⟨h, hh⟩ := exists_homeomorph_of_clopen_orderIso (fun U hU => (hθ U hU).1) hθo hθs
  refine ⟨h, fun g x => ?_⟩
  by_contra hne
  obtain ⟨W, hW, hW1, hW2⟩ := exists_isClopen_separating hne
  obtain ⟨U, hU, rfl⟩ := hθs W hW
  have hgU : IsClopen ((g : X ≃ₜ X) ⁻¹' U) := hU.preimage (g : X ≃ₜ X).continuous
  have h1 : h x ∈ θ ((g : X ≃ₜ X) ⁻¹' U) := by
    rw [hequiv g U hU]
    exact hW1
  have h2 : x ∈ (g : X ≃ₜ X) ⁻¹' U := (hh x _ hgU).1 h1
  exact hW2 ((hh ((g : X ≃ₜ X) x) U hU).2 h2)

/-- The reduction of spatial realization to the transport of rigid stabilizers. -/
theorem spatialRealization_of_rigidStabilizerTransport
    (hrs : RigidStabilizerTransportStatement) : SpatialRealizationStatement :=
  fun X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ T S hT hS Φ =>
    spatiallyImplemented_of_rigidStabilizerTransport hT hS Φ (hrs X Y T S hT hS Φ)
      (hrs Y X S T hS hT Φ.symm)

/-- The printed converse for topological full groups of Cantor minimal systems, reduced to the
single remaining gap `RigidStabilizerTransportStatement`. -/
theorem manuscriptSentence_flipConjugateConverse_of_rigidStabilizerTransport
    (hrs : RigidStabilizerTransportStatement) {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [PerfectSpace X] [Nonempty X] [TopologicalSpace.MetrizableSpace X] [CompactSpace Y]
    [T2Space Y] [TotallyDisconnectedSpace Y] [PerfectSpace Y] [Nonempty Y]
    [TopologicalSpace.MetrizableSpace Y] {T : X ≃ₜ X} {S : Y ≃ₜ Y}
    (hT : IsMinimalHomeo T) (hS : IsMinimalHomeo S) :
    Nonempty (topologicalFullGroup T ≃* topologicalFullGroup S) ↔ FlipConjugate T S :=
  manuscriptSentence_flipConjugateConverse_of_spatialRealization
    (spatialRealization_of_rigidStabilizerTransport hrs) hT hS

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.spatiallyImplemented_of_rigidStabilizerTransport
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.spatialRealization_of_rigidStabilizerTransport
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.manuscriptSentence_flipConjugateConverse_of_rigidStabilizerTransport
