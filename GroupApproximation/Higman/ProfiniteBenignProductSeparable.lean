import GroupApproximation.Higman.ProfiniteBenignWitness

/-!
# Product separation for strengthened benign witnesses

The two Pinch stages in Higman's join must separate elements from the set
product of the embedded source range and the cutting subgroup.  Closedness of
the two factors does not imply this property, so it is recorded separately.
-/

namespace GroupApproximation
namespace Higman

noncomputable section

open scoped Pointwise

variable {G K N : Type} [Group G] [Group K] [Group N]

/-- Every point outside `A * B` stays outside the product of the two images in
some finite quotient. -/
def SetProductSeparable (A B : Subgroup G) : Prop :=
  ∀ x : G, x ∉ (A : Set G) * (B : Set G) →
    ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (q : G →* Q),
      q x ∉ (A.map q : Set Q) * (B.map q : Set Q)

/-- The relative product-separation invariant needed by a benign cutter. -/
def ProfiniteBenignWitness.ProductSeparable {H : Subgroup G}
    (u : ProfiniteBenignWitness H) : Prop :=
  SetProductSeparable u.witness.emb.range u.witness.L

namespace ProfiniteBenignWitness.ProductSeparable

variable {H : Subgroup N} (u : ProfiniteBenignWitness H)

/-- Product separation survives the direct-product preimage construction
when the source map is surjective.  This is the exact constructor used by
`hprodModel`, whose source map is first projection. -/
theorem comap_of_surjective
    (hu : u.ProductSeparable)
    (v : ProfiniteFPOvergroup G) (phi : G →* N)
    (hphi : Function.Surjective phi) :
    (ProfiniteBenignWitness.comap v phi u).ProductSeparable := by
  intro x hx
  have hx₂ : x.2 ∉
      (u.witness.emb.range : Set u.witness.K) *
        (u.witness.L : Set u.witness.K) := by
    intro hmem
    obtain ⟨a, ⟨n, rfl⟩, l, hl, hal⟩ := hmem
    obtain ⟨g, rfl⟩ := hphi n
    apply hx
    refine ⟨(v.overgroup.emb g, u.witness.emb (phi g)), ?_,
      ((v.overgroup.emb g)⁻¹ * x.1, l), ?_, ?_⟩
    · exact ⟨g, rfl⟩
    · exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, hl⟩
    · apply Prod.ext
      · dsimp
        exact mul_inv_cancel_left _ _
      · exact hal
  obtain ⟨Q, hQgroup, hQfinite, q, hq⟩ := hu x.2 hx₂
  refine ⟨Q, hQgroup, hQfinite,
    q.comp (MonoidHom.snd v.overgroup.K u.witness.K), ?_⟩
  intro hmem
  obtain ⟨a, ha, l, hl, hal⟩ := hmem
  obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨l₀, hl₀, rfl⟩ := Subgroup.mem_map.mp hl
  obtain ⟨g, hga⟩ := ha₀
  subst a₀
  have hl₂ : l₀.2 ∈ u.witness.L := (Subgroup.mem_prod.mp hl₀).2
  apply hq
  refine ⟨q (u.witness.emb (phi g)), ⟨u.witness.emb (phi g), ⟨phi g, rfl⟩, rfl⟩,
    q l₀.2, ⟨l₀.2, hl₂, rfl⟩, ?_⟩
  exact hal

end ProfiniteBenignWitness.ProductSeparable

end

end Higman
end GroupApproximation
