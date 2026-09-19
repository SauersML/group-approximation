/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GroupApproximation.BHPalomar.GraphProducts.ProductClosure

/-!
# `ProductInput` holds

`isTypeA_sum`: if `Γ₁ ↷ S₁` and `Γ₂ ↷ S₂` are of type (A), then so is `Γ₁ × Γ₂ ↷ S₁ ⊕ S₂`.
Hence `productInput_holds`: PBH is closed under direct products (Zaremsky, Proposition 5.5).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

namespace GroupApproximation.BHPalomar.GraphProducts

attribute [local instance] sumProdAction

section

variable {Γ₁ Γ₂ S₁ S₂ : Type} [Group Γ₁] [Group Γ₂] [MulAction Γ₁ S₁] [MulAction Γ₂ S₂]

theorem pair_smul_ll (g : Γ₁) (f : S₁ × S₁) :
    ((g, (1 : Γ₂)) : Γ₁ × Γ₂) • ((Sum.inl f.1, Sum.inl f.2) : (S₁ ⊕ S₂) × (S₁ ⊕ S₂)) =
      (Sum.inl (g • f).1, Sum.inl (g • f).2) := rfl

theorem pair_smul_rr (g : Γ₂) (f : S₂ × S₂) :
    (((1 : Γ₁), g) : Γ₁ × Γ₂) • ((Sum.inr f.1, Sum.inr f.2) : (S₁ ⊕ S₂) × (S₁ ⊕ S₂)) =
      (Sum.inr (g • f).1, Sum.inr (g • f).2) := rfl

theorem pair_smul_lr (g₁ : Γ₁) (g₂ : Γ₂) (p : S₁) (q : S₂) :
    ((g₁, g₂) : Γ₁ × Γ₂) • ((Sum.inl p, Sum.inr q) : (S₁ ⊕ S₂) × (S₁ ⊕ S₂)) =
      (Sum.inl (g₁ • p), Sum.inr (g₂ • q)) := rfl

theorem pair_smul_rl (g₁ : Γ₁) (g₂ : Γ₂) (q : S₂) (p : S₁) :
    ((g₁, g₂) : Γ₁ × Γ₂) • ((Sum.inr q, Sum.inl p) : (S₁ ⊕ S₂) × (S₁ ⊕ S₂)) =
      (Sum.inr (g₂ • q), Sum.inl (g₁ • p)) := rfl

theorem point_reps {Γ S : Type} [Group Γ] [MulAction Γ S] {F : Set (S × S)}
    (hr : ∀ x, ∃ f ∈ F, ∃ g : Γ, g • f = x) (a : S) : ∃ p ∈ Prod.fst '' F, ∃ g : Γ, g • p = a := by
  obtain ⟨f, hf, g, hg⟩ := hr (a, a)
  exact ⟨f.1, ⟨f, hf, rfl⟩, g, by rw [← Prod.smul_fst, hg]⟩

/-- **The disjoint union of two actions of type (A) is of type (A).** -/
theorem isTypeA_sum (h₁ : IsTypeA Γ₁ S₁) (h₂ : IsTypeA Γ₂ S₂) : IsTypeA (Γ₁ × Γ₂) (S₁ ⊕ S₂) := by
  obtain ⟨f₁, p₁, s₁, o₁⟩ := h₁
  obtain ⟨f₂, p₂, s₂, o₂⟩ := h₂
  refine ⟨⟨fun {g h} hgh => Prod.ext ?_ ?_⟩, isFinitelyPresented_prod Γ₁ Γ₂, ?_, ?_⟩
  · refine FaithfulSMul.eq_of_smul_eq_smul fun s => ?_
    have h1 := hgh (Sum.inl s)
    rw [sum_smul_inl, sum_smul_inl] at h1
    exact Sum.inl_injective h1
  · refine FaithfulSMul.eq_of_smul_eq_smul fun t => ?_
    have h1 := hgh (Sum.inr t)
    rw [sum_smul_inr, sum_smul_inr] at h1
    exact Sum.inr_injective h1
  · intro x
    cases x with
    | inl s =>
      have hst : MulAction.stabilizer (Γ₁ × Γ₂) (Sum.inl s : S₁ ⊕ S₂) =
          (MulAction.stabilizer Γ₁ s).prod ⊤ := by
        ext g
        rw [MulAction.mem_stabilizer_iff, sum_smul_inl, Sum.inl.injEq, Subgroup.mem_prod,
          MulAction.mem_stabilizer_iff]
        simp
      rw [hst]
      exact (s₁ s).prod (fg_top_of_fp Γ₂)
    | inr t =>
      have hst : MulAction.stabilizer (Γ₁ × Γ₂) (Sum.inr t : S₁ ⊕ S₂) =
          (⊤ : Subgroup Γ₁).prod (MulAction.stabilizer Γ₂ t) := by
        ext g
        rw [MulAction.mem_stabilizer_iff, sum_smul_inr, Sum.inr.injEq, Subgroup.mem_prod,
          MulAction.mem_stabilizer_iff]
        simp
      rw [hst]
      exact (fg_top_of_fp Γ₁).prod (s₂ t)
  · obtain ⟨F₁, hF₁, hr₁⟩ := finite_orbits_iff.mp o₁
    obtain ⟨F₂, hF₂, hr₂⟩ := finite_orbits_iff.mp o₂
    refine finite_orbits_iff.mpr ⟨
      (Prod.map Sum.inl Sum.inl) '' F₁ ∪ (Prod.map Sum.inr Sum.inr) '' F₂ ∪
        (fun p : S₁ × S₂ => ((Sum.inl p.1 : S₁ ⊕ S₂), (Sum.inr p.2 : S₁ ⊕ S₂))) ''
          (Prod.fst '' F₁ ×ˢ Prod.fst '' F₂) ∪
        (fun p : S₂ × S₁ => ((Sum.inr p.1 : S₁ ⊕ S₂), (Sum.inl p.2 : S₁ ⊕ S₂))) ''
          (Prod.fst '' F₂ ×ˢ Prod.fst '' F₁),
      (((hF₁.image _).union (hF₂.image _)).union (((hF₁.image _).prod (hF₂.image _)).image _)).union
        (((hF₂.image _).prod (hF₁.image _)).image _), ?_⟩
    rintro ⟨x, y⟩
    cases x with
    | inl a =>
      cases y with
      | inl b =>
        obtain ⟨f, hf, g, hg⟩ := hr₁ (a, b)
        refine ⟨(Sum.inl f.1, Sum.inl f.2), Or.inl (Or.inl (Or.inl ⟨f, hf, rfl⟩)), (g, 1), ?_⟩
        rw [pair_smul_ll, hg]
      | inr b =>
        obtain ⟨p, hp, g₁, hg₁⟩ := point_reps hr₁ a
        obtain ⟨q, hq, g₂, hg₂⟩ := point_reps hr₂ b
        refine ⟨(Sum.inl p, Sum.inr q), Or.inl (Or.inr ⟨(p, q), ⟨hp, hq⟩, rfl⟩), (g₁, g₂), ?_⟩
        rw [pair_smul_lr, hg₁, hg₂]
    | inr a =>
      cases y with
      | inl b =>
        obtain ⟨q, hq, g₂, hg₂⟩ := point_reps hr₂ a
        obtain ⟨p, hp, g₁, hg₁⟩ := point_reps hr₁ b
        refine ⟨(Sum.inr q, Sum.inl p), Or.inr ⟨(q, p), ⟨hq, hp⟩, rfl⟩, (g₁, g₂), ?_⟩
        rw [pair_smul_rl, hg₁, hg₂]
      | inr b =>
        obtain ⟨f, hf, g, hg⟩ := hr₂ (a, b)
        refine ⟨(Sum.inr f.1, Sum.inr f.2), Or.inl (Or.inl (Or.inr ⟨f, hf, rfl⟩)), (1, g), ?_⟩
        rw [pair_smul_rr, hg]

end

/-- **`ProductInput` holds**: PBH is closed under direct products. -/
theorem productInput_holds : ProductInput := by
  intro A B _ _ hA hB
  obtain ⟨Γ₁, _, S₁, _, h₁, f₁, hf₁⟩ := hA
  obtain ⟨Γ₂, _, S₂, _, h₂, f₂, hf₂⟩ := hB
  exact ⟨Γ₁ × Γ₂, inferInstance, S₁ ⊕ S₂, sumProdAction Γ₁ Γ₂ S₁ S₂, isTypeA_sum h₁ h₂,
    MonoidHom.prodMap f₁ f₂, fun x y hxy => by
      have h1 : f₁ x.1 = f₁ y.1 := congrArg Prod.fst hxy
      have h2 : f₂ x.2 = f₂ y.2 := congrArg Prod.snd hxy
      exact Prod.ext (hf₁ h1) (hf₂ h2)⟩

end GroupApproximation.BHPalomar.GraphProducts
