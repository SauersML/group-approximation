import GroupApproximation.Higman.BenignJoin

/-!
# Exact generated form of Higman's benign join cutter

The subgroup called `joinS₂` in the two Britton descents is not merely an
overgroup of the finitely generated cutter `joinL`: the two subgroups are
equal.  This exposes the cutter as the two successive pinch-generated
subgroups used by its Britton proof, which is the normal form needed by
finite-quotient reflection.
-/

namespace GroupApproximation
namespace Higman

noncomputable section

variable {G : Type} [Group G] {A₁ A₂ : Subgroup G}
variable (w₁ : BenignWitness A₁) (w₂ : BenignWitness A₂)

/-- The transported copy of `joinZ₁ = A₁ ⊔ A₂` is already contained in
`joinL`. -/
theorem of_of_mem_joinL_of_mem_joinZ₁ {z : JoinBase w₁ w₂}
    (hz : z ∈ joinZ₁ w₁ w₂) :
    (HNNExtension.of (HNNExtension.of z : JoinLevel1 w₁ w₂) :
      JoinLevel2 w₁ w₂) ∈ joinL w₁ w₂ := by
  obtain ⟨g, hg, rfl⟩ := hz
  exact Subgroup.mem_comap.mp (join_le_comap_joinL w₁ w₂ hg)

/-- The whole first-stage subgroup, transported through the second base map,
lies in `joinL`. -/
theorem of_mem_joinL_of_mem_joinS₁ {x : JoinLevel1 w₁ w₂}
    (hx : x ∈ joinS₁ w₁ w₂) :
    (HNNExtension.of x : JoinLevel2 w₁ w₂) ∈ joinL w₁ w₂ := by
  refine Subgroup.closure_induction
    (p := fun y _ ↦
      (HNNExtension.of y : JoinLevel2 w₁ w₂) ∈ joinL w₁ w₂)
    ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with hy | hy
    · obtain ⟨z, hz, rfl⟩ := hy
      exact of_of_mem_joinL_of_mem_joinZ₁ w₁ w₂ hz
    · obtain ⟨q, hq, rfl⟩ := hy
      obtain ⟨z, hz, rfl⟩ := hq
      obtain ⟨g, -, rfl⟩ := hz
      refine Subgroup.mem_sup_left ⟨joinEmb₂ w₁ w₂ g,
        ⟨g, Subgroup.mem_top g, rfl⟩, ?_⟩
      simp [conjT_apply, joinEmb₂]
  · rw [map_one]
    exact Subgroup.one_mem _
  · intro y z _ _ hy hz
    rw [map_mul]
    exact Subgroup.mul_mem _ hy hz
  · intro y _ hy
    rw [map_inv]
    exact Subgroup.inv_mem _ hy

/-- The second conjugate generator in `joinS₂` belongs to the second
summand defining `joinL`. -/
theorem mem_joinL_of_mem_second_gen {y : JoinLevel2 w₁ w₂}
    (hy : y ∈
      ((joinQ₂ w₁ w₂).map
        (HNNExtension.of : JoinLevel1 w₁ w₂ →* JoinLevel2 w₁ w₂)).map
          (conjT (joinM₂' w₁ w₂)).toMonoidHom) :
    y ∈ joinL w₁ w₂ := by
  obtain ⟨q, hq, rfl⟩ := hy
  obtain ⟨z, hz, rfl⟩ := hq
  obtain ⟨g, -, rfl⟩ := hz
  refine Subgroup.mem_sup_right ⟨joinEmb₂ w₁ w₂ g,
    ⟨g, Subgroup.mem_top g, rfl⟩, ?_⟩
  simp [conjT_apply, joinEmb₂]

/-- **Exact generated form of the join cutter.**  The auxiliary subgroup
`joinS₂` used for the two Britton descents is precisely `joinL`. -/
theorem joinL_eq_joinS₂ : joinL w₁ w₂ = joinS₂ w₁ w₂ := by
  apply le_antisymm (joinL_le_joinS₂ w₁ w₂)
  intro x hx
  refine Subgroup.closure_induction (p := fun y _ ↦ y ∈ joinL w₁ w₂)
    ?_ (Subgroup.one_mem _) (fun _ _ _ _ ↦ Subgroup.mul_mem _)
    (fun _ _ ↦ Subgroup.inv_mem _) hx
  intro y hy
  rcases hy with hy | hy
  · obtain ⟨x, hx, rfl⟩ := hy
    exact of_mem_joinL_of_mem_joinS₁ w₁ w₂ hx
  · exact mem_joinL_of_mem_second_gen w₁ w₂ hy

end

end Higman
end GroupApproximation
