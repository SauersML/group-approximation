import GroupApproximation.Higman.ProfiniteBenignWitness

/-!
# Closed subgroups under cofinal profinite embeddings

A closed embedding whose restricted finite quotients are cofinal carries every
closed source subgroup to a closed subgroup of the target.  This is the exact
base-quotient descent needed before applying finite-base HNN separability to
the two stages of the special benign join.
-/

namespace GroupApproximation
namespace Higman

noncomputable section

variable {G K : Type} [Group G] [Group K]

/-- A closed subgroup stays closed under an injective embedding with closed
range and cofinally extending finite quotients. -/
theorem profiniteClosure_map_eq_of_cofinal_closedRange
    (f : G →* K)
    (hcofinal : CofinalProfiniteEmbedding f)
    (hrange : profiniteClosure f.range = f.range)
    (A : Subgroup G) (hA : profiniteClosure A = A) :
    profiniteClosure (A.map f) = A.map f := by
  apply le_antisymm
  · intro z hz
    have hzrange : z ∈ profiniteClosure f.range :=
      profiniteClosure_mono (by
        rintro _ ⟨a, -, rfl⟩
        exact ⟨a, rfl⟩) hz
    rw [hrange] at hzrange
    obtain ⟨g, rfl⟩ := hzrange
    have hgclose : g ∈ profiniteClosure A := by
      intro Q _ _ q
      obtain ⟨R, hRgroup, hRfinite, p, hp⟩ := hcofinal Q q
      letI : Group R := hRgroup
      letI : Finite R := hRfinite
      have hpf : p (f g) ∈ (A.map f).map p := hz R p
      obtain ⟨_, ⟨a, ha, rfl⟩, hpa⟩ := Subgroup.mem_map.mp hpf
      refine ⟨a, ha, ?_⟩
      have hker : a⁻¹ * g ∈ p.ker.comap f := by
        change p (f (a⁻¹ * g)) = 1
        simp only [map_mul, map_inv, hpa, inv_mul_cancel]
      have hqker := hp hker
      change q (a⁻¹ * g) = 1 at hqker
      rw [map_mul, map_inv] at hqker
      exact inv_mul_eq_one.mp hqker
    rw [hA] at hgclose
    exact ⟨g, hgclose, rfl⟩
  · exact le_profiniteClosure (A.map f)

/-- The source join, transported into the product base of two strengthened
benign witnesses, is closed as soon as the source join itself is closed. -/
theorem profiniteClosure_joinZ₁_of_source_closed
    {A₁ A₂ : Subgroup G}
    (u₁ : ProfiniteBenignWitness A₁)
    (u₂ : ProfiniteBenignWitness A₂)
    (hsource : profiniteClosure (A₁ ⊔ A₂) = A₁ ⊔ A₂) :
    profiniteClosure (joinZ₁ u₁.witness u₂.witness) =
      joinZ₁ u₁.witness u₂.witness := by
  exact profiniteClosure_map_eq_of_cofinal_closedRange
    (joinEmb u₁.witness u₂.witness)
    (ProfiniteBenignJoin.baseEmbedding_cofinal u₁ u₂)
    (ProfiniteBenignJoin.baseEmbedding_closed u₁ u₂)
    (A₁ ⊔ A₂) hsource

end

end Higman
end GroupApproximation
