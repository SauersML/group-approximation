import GroupApproximation.Higman.ProfiniteBenignFactorizationReflection

/-!
# Product separation through the benign Inf construction

For a diagonal product witness, coordinatewise product separation is not
enough: two coordinate factorizations may use different source elements.
Prescribed cutter reflection on both coordinates, together with separation of
the source product `H₁ * H₂`, synchronizes those elements in one finite
quotient.
-/

namespace GroupApproximation
namespace Higman

noncomputable section

open scoped Pointwise

variable {G : Type} [Group G] {H₁ H₂ : Subgroup G}

/-- The precise synchronization datum needed by an Inf witness.  For every
failed source factorization, one finite source quotient both detects the
failure and admits cutter-factorization reflection on the two witness sides.

Unlike demanding uniform reflection of both witnesses, this permits the
second witness to be a comap/hprod witness, which only reflects quotients
factoring through its source coordinate map. -/
def ProfiniteBenignWitness.InfSynchronizing
    (u₁ : ProfiniteBenignWitness H₁) (u₂ : ProfiniteBenignWitness H₂) : Prop :=
  ∀ d : G, d ∉ (H₁ : Set G) * (H₂ : Set G) →
    ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (q : G →* Q),
      q d ∉ (H₁.map q : Set Q) * (H₂.map q : Set Q) ∧
      u₁.FactorizationReflectingAt Q q ∧
      u₂.FactorizationReflectingAt Q q

namespace ProfiniteBenignWitness.ProductSeparable

/-- Honest propagation of range--cutter product separation through Inf. -/
theorem inf
    (u₁ : ProfiniteBenignWitness H₁) (u₂ : ProfiniteBenignWitness H₂)
    (hp₁ : u₁.ProductSeparable) (hp₂ : u₂.ProductSeparable)
    (hsync : u₁.InfSynchronizing u₂) :
    (u₁.inf u₂).ProductSeparable := by
  change SetProductSeparable
    (u₁.witness.inf u₂.witness).emb.range
    (u₁.witness.inf u₂.witness).L
  unfold SetProductSeparable
  dsimp only [BenignWitness.inf]
  intro x hx
  by_cases hx₁ : x.1 ∈
      (u₁.witness.emb.range : Set u₁.witness.K) *
        (u₁.witness.L : Set u₁.witness.K)
  · by_cases hx₂ : x.2 ∈
        (u₂.witness.emb.range : Set u₂.witness.K) *
          (u₂.witness.L : Set u₂.witness.K)
    · obtain ⟨a₁, ⟨g₁, rfl⟩, l₁, hl₁, hxl₁⟩ := hx₁
      obtain ⟨a₂, ⟨g₂, rfl⟩, l₂, hl₂, hxl₂⟩ := hx₂
      have hd : g₁⁻¹ * g₂ ∉ (H₁ : Set G) * (H₂ : Set G) := by
        intro hdmem
        obtain ⟨h₁, hh₁, h₂, hh₂, hdEq⟩ := hdmem
        apply hx
        refine ⟨(u₁.witness.emb (g₁ * h₁),
            u₂.witness.emb (g₁ * h₁)),
          ⟨g₁ * h₁, rfl⟩,
          (u₁.witness.emb h₁⁻¹ * l₁,
            u₂.witness.emb h₂ * l₂), ?_, ?_⟩
        · exact Subgroup.mem_prod.mpr ⟨u₁.witness.L.mul_mem
            (by
              rw [map_inv]
              exact u₁.witness.L.inv_mem
                (Subgroup.mem_comap.mp (show h₁ ∈
                    u₁.witness.L.comap u₁.witness.emb by
                  rw [u₁.witness.comap_eq]
                  exact hh₁))) hl₁,
            u₂.witness.L.mul_mem
            (Subgroup.mem_comap.mp (show h₂ ∈ u₂.witness.L.comap u₂.witness.emb by
              rw [u₂.witness.comap_eq]
              exact hh₂)) hl₂⟩
        · change
            (u₁.witness.emb (g₁ * h₁) *
                (u₁.witness.emb h₁⁻¹ * l₁),
              u₂.witness.emb (g₁ * h₁) *
                (u₂.witness.emb h₂ * l₂)) = x
          apply Prod.ext
          · change u₁.witness.emb (g₁ * h₁) *
                (u₁.witness.emb h₁⁻¹ * l₁) = x.1
            rw [← mul_assoc, ← map_mul]
            simp only [mul_inv_cancel_right]
            exact hxl₁
          · change u₂.witness.emb (g₁ * h₁) *
                (u₂.witness.emb h₂ * l₂) = x.2
            rw [← mul_assoc, ← map_mul]
            have hg : g₁ * h₁ * h₂ = g₂ := by
              calc
                g₁ * h₁ * h₂ = g₁ * (h₁ * h₂) := by group
                _ = g₁ * (g₁⁻¹ * g₂) :=
                  congrArg (fun z ↦ g₁ * z) hdEq
                _ = g₂ := by group
            rw [hg]
            exact hxl₂
      obtain ⟨Q, hQgroup, hQfinite, q, hq, href₁, href₂⟩ :=
        hsync (g₁⁻¹ * g₂) hd
      letI : Group Q := hQgroup
      letI : Finite Q := hQfinite
      obtain ⟨R₁, hR₁group, hR₁finite, p₁, hp₁reflect⟩ := href₁
      letI : Group R₁ := hR₁group
      letI : Finite R₁ := hR₁finite
      obtain ⟨R₂, hR₂group, hR₂finite, p₂, hp₂reflect⟩ := href₂
      refine ⟨R₁ × R₂, inferInstance, inferInstance, p₁.prodMap p₂, ?_⟩
      intro hmem
      obtain ⟨a, ha, l, hl, hal⟩ := hmem
      obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨g, rfl⟩ := ha₀
      obtain ⟨l₀, hl₀, rfl⟩ := Subgroup.mem_map.mp hl
      change
        (p₁ (u₁.witness.emb g) * p₁ l₀.1,
          p₂ (u₂.witness.emb g) * p₂ l₀.2) =
        (p₁ x.1, p₂ x.2) at hal
      have hl₀₁ : l₀.1 ∈ u₁.witness.L := (Subgroup.mem_prod.mp hl₀).1
      have hl₀₂ : l₀.2 ∈ u₂.witness.L := (Subgroup.mem_prod.mp hl₀).2
      have hfactor₁ : p₁ (u₁.witness.emb (g⁻¹ * g₁)) ∈
          u₁.witness.L.map p₁ := by
        refine ⟨l₀.1 * l₁⁻¹, u₁.witness.L.mul_mem hl₀₁
          (u₁.witness.L.inv_mem hl₁), ?_⟩
        have heq : p₁ (u₁.witness.emb g) * p₁ l₀.1 = p₁ x.1 :=
          congrArg Prod.fst hal
        rw [← hxl₁] at heq
        simp only [map_mul, map_inv] at heq ⊢
        change p₁ l₀.1 * (p₁ l₁)⁻¹ =
          (p₁ (u₁.witness.emb g))⁻¹ * p₁ (u₁.witness.emb g₁)
        have heq' := congrArg
          (fun z ↦ (p₁ (u₁.witness.emb g))⁻¹ * z * (p₁ l₁)⁻¹) heq
        group at heq'
        simpa only [zpow_neg_one] using heq'
      have hfactor₂ : p₂ (u₂.witness.emb (g⁻¹ * g₂)) ∈
          u₂.witness.L.map p₂ := by
        refine ⟨l₀.2 * l₂⁻¹, u₂.witness.L.mul_mem hl₀₂
          (u₂.witness.L.inv_mem hl₂), ?_⟩
        have heq : p₂ (u₂.witness.emb g) * p₂ l₀.2 = p₂ x.2 :=
          congrArg Prod.snd hal
        rw [← hxl₂] at heq
        simp only [map_mul, map_inv] at heq ⊢
        change p₂ l₀.2 * (p₂ l₂)⁻¹ =
          (p₂ (u₂.witness.emb g))⁻¹ * p₂ (u₂.witness.emb g₂)
        have heq' := congrArg
          (fun z ↦ (p₂ (u₂.witness.emb g))⁻¹ * z * (p₂ l₂)⁻¹) heq
        group at heq'
        simpa only [zpow_neg_one] using heq'
      have hq₁ := hp₁reflect (g⁻¹ * g₁) hfactor₁
      have hq₂ := hp₂reflect (g⁻¹ * g₂) hfactor₂
      apply hq
      refine ⟨(q (g⁻¹ * g₁))⁻¹, ?_, q (g⁻¹ * g₂), hq₂, ?_⟩
      · exact Subgroup.inv_mem _ hq₁
      · simp only [map_mul, map_inv]
        group
    · obtain ⟨Q, hQgroup, hQfinite, q, hq⟩ := hp₂ x.2 hx₂
      refine ⟨Q, hQgroup, hQfinite,
        q.comp (MonoidHom.snd u₁.witness.K u₂.witness.K), ?_⟩
      intro hmem
      obtain ⟨a, ha, l, hl, hal⟩ := hmem
      obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨g, rfl⟩ := ha₀
      obtain ⟨l₀, hl₀, rfl⟩ := Subgroup.mem_map.mp hl
      apply hq
      refine ⟨q (u₂.witness.emb g), ⟨u₂.witness.emb g, ⟨g, rfl⟩, rfl⟩,
        q l₀.2, ⟨l₀.2, (Subgroup.mem_prod.mp hl₀).2, rfl⟩, ?_⟩
      exact hal
  · obtain ⟨Q, hQgroup, hQfinite, q, hq⟩ := hp₁ x.1 hx₁
    refine ⟨Q, hQgroup, hQfinite,
      q.comp (MonoidHom.fst u₁.witness.K u₂.witness.K), ?_⟩
    intro hmem
    obtain ⟨a, ha, l, hl, hal⟩ := hmem
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨g, rfl⟩ := ha₀
    obtain ⟨l₀, hl₀, rfl⟩ := Subgroup.mem_map.mp hl
    apply hq
    refine ⟨q (u₁.witness.emb g), ⟨u₁.witness.emb g, ⟨g, rfl⟩, rfl⟩,
      q l₀.1, ⟨l₀.1, (Subgroup.mem_prod.mp hl₀).1, rfl⟩, ?_⟩
    exact hal

end ProfiniteBenignWitness.ProductSeparable

end

end Higman
end GroupApproximation
