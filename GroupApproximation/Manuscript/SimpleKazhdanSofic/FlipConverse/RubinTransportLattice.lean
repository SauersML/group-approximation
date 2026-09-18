import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RubinPolarOpenTransport
import GroupApproximation.Meta.AxiomGuard

/-!
# Rubin transport, part 1: open transport is closed under finite unions

Lane `sk-flip-20`.  We fix an isomorphism `Φ : [[T]] ≃* [[S]]` of topological full groups of
minimal systems, and say that a clopen `U ⊆ X` is *open-transported* when
`Φ F_U = F_O` for some open `O ⊆ Y` (`F_O = rubinRigidSubgroup S O`).

* `rubinRigidSubgroup_inf_eq_inter`: `F_A ⊓ F_B = F_{A ∩ B}` for all sets `A, B`.
* `rubinTransport_rigid_empty`: `∅` is open-transported.  Proof: `F_∅ = C(F_univ)`,
  `Φ F_univ = ⊤ = F_univ`, and `Φ` commutes with centralisers.
* `rubinTransport_rigid_union`: if `U₁, U₂` are clopen with `Φ F_{U_i} = F_{O_i}` and the `O_i`
  open, then `U₁ ∪ U₂` is open-transported, with
  `O = interior (interior (O₁ᶜ ∩ O₂ᶜ))ᶜ`.  On the source side
  `F_{U₁ ∪ U₂} = C(C(F_{U₁}) ⊓ C(F_{U₂}))`, because `C(F_{U_i}) = F_{U_iᶜ}`, then
  `F_{U₁ᶜ} ⊓ F_{U₂ᶜ} = F_{(U₁ ∪ U₂)ᶜ}`, and `(U₁ ∪ U₂)ᶜ` is open.  Transporting through `Φ`
  (`rubinTransport_centralizer`, `rubinTransport_inf`) gives `C(F_{O₁ᶜ ∩ O₂ᶜ})`.  Rigid stabilisers
  do not see interiors (`rubinRigidSubgroup_interior`), so the centraliser formula applies to the
  open set `interior (O₁ᶜ ∩ O₂ᶜ)`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

section RubinTransportLattice

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Rigid stabilisers turn intersections of sets into infima of subgroups. -/
theorem rubinRigidSubgroup_inf_eq_inter (T : X ≃ₜ X) (A B : Set X) :
    rubinRigidSubgroup T A ⊓ rubinRigidSubgroup T B = rubinRigidSubgroup T (A ∩ B) := by
  ext g
  rw [Subgroup.mem_inf, mem_rubinRigidSubgroup, mem_rubinRigidSubgroup, mem_rubinRigidSubgroup]
  constructor
  · rintro ⟨h₁, h₂⟩ x hx
    by_cases hA : x ∈ A
    · exact h₂ x fun hB => hx ⟨hA, hB⟩
    · exact h₁ x hA
  · intro h
    exact ⟨h.mono Set.inter_subset_left, h.mono Set.inter_subset_right⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinRigidSubgroup_inf_eq_inter

variable [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] [PerfectSpace X]
  [CompactSpace Y] [T2Space Y] [TotallyDisconnectedSpace Y] [PerfectSpace Y]
  {T : X ≃ₜ X} {S : Y ≃ₜ Y}

/-- The empty set is open-transported by every isomorphism of topological full groups. -/
theorem rubinTransport_rigid_empty (hT : IsMinimalHomeo T) (hS : IsMinimalHomeo S)
    (Φ : topologicalFullGroup T ≃* topologicalFullGroup S) :
    ∃ O : Set Y, IsOpen O ∧
      rubinTransport Φ (rubinRigidSubgroup T (∅ : Set X)) = rubinRigidSubgroup S O := by
  refine ⟨∅, isOpen_empty, ?_⟩
  have hu : rubinTransport Φ (rubinRigidSubgroup T (Set.univ : Set X)) =
      rubinRigidSubgroup S (Set.univ : Set Y) := by
    ext k
    rw [mem_rubinTransport, mem_rubinRigidSubgroup, mem_rubinRigidSubgroup]
    exact ⟨fun _ y hy => absurd (Set.mem_univ y) hy, fun _ x hx => absurd (Set.mem_univ x) hx⟩
  have h0 : rubinRigidSubgroup T (∅ : Set X) =
      Subgroup.centralizer (rubinRigidSubgroup T (Set.univ : Set X) :
        Set (topologicalFullGroup T)) := by
    rw [centralizer_rubinRigidSubgroup hT isOpen_univ, Set.compl_univ]
  have h0' : rubinRigidSubgroup S (∅ : Set Y) =
      Subgroup.centralizer (rubinRigidSubgroup S (Set.univ : Set Y) :
        Set (topologicalFullGroup S)) := by
    rw [centralizer_rubinRigidSubgroup hS isOpen_univ, Set.compl_univ]
  rw [h0, h0', ← rubinTransport_centralizer, hu]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinTransport_rigid_empty

/-- Open transport is closed under unions of two clopen sets. -/
theorem rubinTransport_rigid_union (hT : IsMinimalHomeo T) (hS : IsMinimalHomeo S)
    (Φ : topologicalFullGroup T ≃* topologicalFullGroup S) {U₁ U₂ : Set X} (h₁ : IsClopen U₁)
    (h₂ : IsClopen U₂) {O₁ O₂ : Set Y} (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂)
    (e₁ : rubinTransport Φ (rubinRigidSubgroup T U₁) = rubinRigidSubgroup S O₁)
    (e₂ : rubinTransport Φ (rubinRigidSubgroup T U₂) = rubinRigidSubgroup S O₂) :
    ∃ O : Set Y, IsOpen O ∧
      rubinTransport Φ (rubinRigidSubgroup T (U₁ ∪ U₂)) = rubinRigidSubgroup S O := by
  refine ⟨interior ((interior (O₁ᶜ ∩ O₂ᶜ))ᶜ), isOpen_interior, ?_⟩
  have hX : rubinRigidSubgroup T (U₁ ∪ U₂) =
      Subgroup.centralizer
        ((Subgroup.centralizer (rubinRigidSubgroup T U₁ : Set (topologicalFullGroup T)) ⊓
          Subgroup.centralizer (rubinRigidSubgroup T U₂ : Set (topologicalFullGroup T)) :
            Subgroup (topologicalFullGroup T)) : Set (topologicalFullGroup T)) := by
    rw [centralizer_rubinRigidSubgroup hT h₁.isOpen, centralizer_rubinRigidSubgroup hT h₂.isOpen,
      rubinRigidSubgroup_inf_eq_inter, ← Set.compl_union,
      centralizer_rubinRigidSubgroup hT (isOpen_compl_iff.2 (h₁.union h₂).isClosed),
      compl_compl]
  rw [hX, ← rubinTransport_centralizer, ← rubinTransport_inf, ← rubinTransport_centralizer,
    ← rubinTransport_centralizer, e₁, e₂, centralizer_rubinRigidSubgroup hS hO₁,
    centralizer_rubinRigidSubgroup hS hO₂, rubinRigidSubgroup_inf_eq_inter,
    ← rubinRigidSubgroup_interior (T := S) (S := O₁ᶜ ∩ O₂ᶜ),
    centralizer_rubinRigidSubgroup hS isOpen_interior, rubinRigidSubgroup_interior]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinTransport_rigid_union

end RubinTransportLattice

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse
