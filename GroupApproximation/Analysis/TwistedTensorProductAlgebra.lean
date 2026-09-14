import GroupApproximation.Analysis.TwistedGroupVonNeumannProduct
import GroupApproximation.Meta.AxiomGuard

/-!
# `L_ρ(A) ⊗̄ L_σ(Γ)` is the twisted group von Neumann algebra of `Γ × A`

Infrastructure of lane `oa-mcduff` for `simple_kazhdan_sofic_group.tex` at origin/main 37551fd93,
"Brown's formulation", tex 280–283 (census row `97438886a277`): "`L(G) ⊗̄ 𝓡` is a McDuff factor".

The curry unitary `U : ℓ²(Γ; ℓ²(A)) ≃ ℓ²(Γ × A)` (`Analysis/TwistedGroupVonNeumannProduct`) conjugates
the generators of `L_ρ(A) ⊗̄ L_σ(Γ)` (`Analysis/VonNeumannTwistedAmplification`) to twisted translations
of `Γ × A` for the sum cocycle, and so carries the tensor product onto `L_{σ⊕ρ}(Γ × A)`.

* `entry γ δ Y`: the matrix entry `ev_γ ∘ Y ∘ ι_δ` of an operator on `ℓ²(Γ; H)`; `ext_entry`, and
  commutation with `x ⊗ 1` read off the entries (`commute_ampOperator_of_entry`,
  `entry_commute_of_commute`).
* `curryConj`: `Ad U`.
* `curryConj_twistedShiftOperator`, `curryConj_ampOperator_twistedLeftOperator`: `1 ⊗ λ_σ(γ)` goes to
  `λ(γ, 1)` and `λ_ρ(a) ⊗ 1` to `λ(1, a)`; `twistedLeftOperator_prod_eq_mul`: `λ(γ,a) = λ(γ,1) λ(1,a)`.
* `curryConj_image_twistedTensor`: `Ad U` maps `L_ρ(A) ⊗̄ L_σ(Γ)` onto `L_{σ⊕ρ}(Γ × A)`.
-/

namespace GroupApproximation
namespace TwistedProduct

open ReducedGroupCStarTrace TwistedGroupVonNeumann TwistedTensor
open scoped ENNReal InnerProductSpace

noncomputable section

universe u v w

/-! ## Matrix entries of operators on `ℓ²(Γ; H)` -/

section Entries

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {Γ : Type u} [DecidableEq Γ]

/-- The `(γ, δ)` matrix entry `ev_γ ∘ Y ∘ ι_δ`. -/
def entry (γ δ : Γ) (Y : VecHilbert Γ H →L[ℂ] VecHilbert Γ H) : H →L[ℂ] H :=
  (lp.evalCLM ℂ (fun _ : Γ ↦ H) 2 γ).comp
    (Y.comp (lp.singleContinuousLinearMap ℂ (fun _ : Γ ↦ H) 2 δ))

theorem entry_apply (γ δ : Γ) (Y : VecHilbert Γ H →L[ℂ] VecHilbert Γ H) (w : H) :
    entry γ δ Y w = Y (lp.single 2 δ w) γ :=
  rfl

theorem hasSum_entry (Y : VecHilbert Γ H →L[ℂ] VecHilbert Γ H) (f : VecHilbert Γ H) (γ : Γ) :
    HasSum (fun δ ↦ entry γ δ Y (f δ)) (Y f γ) :=
  (lp.hasSum_single ENNReal.ofNat_ne_top f).mapL ((lp.evalCLM ℂ (fun _ : Γ ↦ H) 2 γ).comp Y)

/-- **An operator on `ℓ²(Γ; H)` is determined by its matrix entries.** -/
theorem ext_entry {Y Z : VecHilbert Γ H →L[ℂ] VecHilbert Γ H}
    (h : ∀ γ δ, entry γ δ Y = entry γ δ Z) : Y = Z := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext γ
  have hY := hasSum_entry Y f γ
  have hZ := hasSum_entry Z f γ
  simp only [h] at hY
  exact hY.unique hZ

theorem ampOperator_single (x : H →L[ℂ] H) (δ : Γ) (w : H) :
    ampOperator Γ x (lp.single 2 δ w) = lp.single 2 δ (x w) := by
  apply lp.ext
  funext ε
  by_cases hε : ε = δ
  · subst hε
    simp only [ampOperator_apply, lp.single_apply, Pi.single_eq_same]
  · simp only [ampOperator_apply, lp.single_apply, Pi.single_eq_of_ne hε, map_zero]

theorem entry_ampOperator_mul (γ δ : Γ) (x : H →L[ℂ] H) (Y : VecHilbert Γ H →L[ℂ] VecHilbert Γ H) :
    entry γ δ (ampOperator Γ x * Y) = x * entry γ δ Y := by
  ext w
  rfl

theorem entry_mul_ampOperator (γ δ : Γ) (x : H →L[ℂ] H) (Y : VecHilbert Γ H →L[ℂ] VecHilbert Γ H) :
    entry γ δ (Y * ampOperator Γ x) = entry γ δ Y * x := by
  ext w
  change Y (ampOperator Γ x (lp.single 2 δ w)) γ = Y (lp.single 2 δ (x w)) γ
  rw [ampOperator_single]

/-- An operator commutes with `x ⊗ 1` when its entries commute with `x`. -/
theorem commute_ampOperator_of_entry (x : H →L[ℂ] H) {Y : VecHilbert Γ H →L[ℂ] VecHilbert Γ H}
    (h : ∀ γ δ, x * entry γ δ Y = entry γ δ Y * x) :
    ampOperator Γ x * Y = Y * ampOperator Γ x := by
  apply ext_entry
  intro γ δ
  rw [entry_ampOperator_mul, entry_mul_ampOperator, h]

/-- The entries of an operator commuting with `s ⊗ 1` commute with `s`. -/
theorem entry_commute_of_commute (s : H →L[ℂ] H) {Y : VecHilbert Γ H →L[ℂ] VecHilbert Γ H}
    (h : ampOperator Γ s * Y = Y * ampOperator Γ s) (γ δ : Γ) :
    s * entry γ δ Y = entry γ δ Y * s := by
  rw [← entry_ampOperator_mul, ← entry_mul_ampOperator, h]

end Entries

/-! ## Centralizers under a multiplicative equivalence -/

theorem centralizer_image_mulEquiv {R S : Type*} [Mul R] [Mul S] (Φ : R ≃* S) (s : Set R) :
    Set.centralizer (Φ '' s) = Φ '' Set.centralizer s := by
  ext y
  constructor
  · intro hy
    refine ⟨Φ.symm y, fun m hm ↦ ?_, Φ.apply_symm_apply y⟩
    apply Φ.injective
    rw [map_mul, map_mul, Φ.apply_symm_apply]
    exact hy (Φ m) ⟨m, hm, rfl⟩
  · rintro ⟨x, hx, rfl⟩ _ ⟨m, hm, rfl⟩
    rw [← map_mul, ← map_mul, hx m hm]

/-! ## The curry conjugation -/

section Conj

variable {Γ : Type u} {A : Type w} [Group Γ] [Group A] (σ : Γ → Γ → ZMod 2) (ρ : A → A → ZMod 2)

/-- `Ad U` for the curry unitary `U : ℓ²(Γ; ℓ²(A)) ≃ ℓ²(Γ × A)`. -/
abbrev curryConj :
    (VecHilbert Γ (GroupHilbert A) →L[ℂ] VecHilbert Γ (GroupHilbert A)) ≃⋆ₐ[ℂ]
      (GroupHilbert (Γ × A) →L[ℂ] GroupHilbert (Γ × A)) :=
  (curryLp (Γ := Γ) (A := A)).conjStarAlgEquiv

theorem curryConj_twistedShiftOperator (hρ : IsSignCocycle ρ) (γ : Γ) :
    curryConj (twistedShiftOperator (H := GroupHilbert A) σ γ) =
      twistedLeftOperator (prodCocycle σ ρ) (γ, 1) := by
  apply ContinuousLinearMap.ext
  intro F
  apply lp.ext
  funext p
  obtain ⟨γ', a'⟩ := p
  show zsign (σ γ (γ⁻¹ * γ')) * F (γ⁻¹ * γ', a') =
    zsign (σ γ (γ⁻¹ * γ') + ρ 1 (1⁻¹ * a')) * F (γ⁻¹ * γ', 1⁻¹ * a')
  rw [inv_one, one_mul, hρ.map_one_left, add_zero]

theorem curryConj_ampOperator_twistedLeftOperator (hσ : IsSignCocycle σ) (a : A) :
    curryConj (ampOperator Γ (twistedLeftOperator ρ a)) =
      twistedLeftOperator (prodCocycle σ ρ) (1, a) := by
  apply ContinuousLinearMap.ext
  intro F
  apply lp.ext
  funext p
  obtain ⟨γ', a'⟩ := p
  show zsign (ρ a (a⁻¹ * a')) * F (γ', a⁻¹ * a') =
    zsign (σ 1 (1⁻¹ * γ') + ρ a (a⁻¹ * a')) * F (1⁻¹ * γ', a⁻¹ * a')
  rw [inv_one, one_mul, hσ.map_one_left, zero_add]

theorem twistedLeftOperator_prod_eq_mul (hσ : IsSignCocycle σ) (hρ : IsSignCocycle ρ)
    (γ : Γ) (a : A) :
    twistedLeftOperator (prodCocycle σ ρ) (γ, a) =
      twistedLeftOperator (prodCocycle σ ρ) (γ, 1) * twistedLeftOperator (prodCocycle σ ρ) (1, a) := by
  rw [twistedLeftOperator_mul (prodCocycle σ ρ) (isSignCocycle_prodCocycle hσ hρ) (γ, 1) (1, a)]
  have h0 : prodCocycle σ ρ (γ, 1) (1, a) = 0 := by
    simp only [prodCocycle, hσ.map_one_right, hρ.map_one_left, add_zero]
  rw [h0, zsign_zero, one_smul]
  congr 1
  exact Prod.ext (mul_one γ).symm (one_mul a).symm

/-- **`Ad U` carries `L_ρ(A) ⊗̄ L_σ(Γ)` onto `L_{σ⊕ρ}(Γ × A)`.** -/
theorem curryConj_image_twistedTensor (hσ : IsSignCocycle σ) (hρ : IsSignCocycle ρ) :
    curryConj '' (twistedTensor (twistedVonNeumannAlgebra ρ) σ :
        Set (VecHilbert Γ (GroupHilbert A) →L[ℂ] VecHilbert Γ (GroupHilbert A))) =
      (twistedVonNeumannAlgebra (prodCocycle σ ρ) : Set (GroupHilbert (Γ × A) →L[ℂ] GroupHilbert (Γ × A))) := by
  classical
  let Φ : (VecHilbert Γ (GroupHilbert A) →L[ℂ] VecHilbert Γ (GroupHilbert A)) ≃*
      (GroupHilbert (Γ × A) →L[ℂ] GroupHilbert (Γ × A)) := (curryConj (Γ := Γ) (A := A)).toMulEquiv
  -- the images of the generators
  have hshift : ∀ γ : Γ, Φ (twistedShiftOperator (H := GroupHilbert A) σ γ) =
      twistedLeftOperator (prodCocycle σ ρ) (γ, 1) := fun γ ↦ curryConj_twistedShiftOperator σ ρ hρ γ
  have hamp : ∀ a : A, Φ (ampOperator Γ (twistedLeftOperator ρ a)) =
      twistedLeftOperator (prodCocycle σ ρ) (1, a) :=
    fun a ↦ curryConj_ampOperator_twistedLeftOperator σ ρ hσ a
  have hstar : ∀ T, Φ (star T) = star (Φ T) := fun T ↦ map_star (curryConj (Γ := Γ) (A := A)) T
  have hcent : Set.centralizer (Φ '' tensorGenerators (twistedVonNeumannAlgebra ρ) σ) =
      Set.centralizer (twistedGenerators (prodCocycle σ ρ)) := by
    apply le_antisymm
    · intro X hX m hm
      have h1 : ∀ γ : Γ, Commute (twistedLeftOperator (prodCocycle σ ρ) (γ, 1)) X := fun γ ↦ by
        rw [← hshift]
        exact hX _ ⟨_, Set.mem_union_right _ (Set.mem_union_left _ ⟨γ, rfl⟩), rfl⟩
      have h2 : ∀ a : A, Commute (twistedLeftOperator (prodCocycle σ ρ) (1, a)) X := fun a ↦ by
        rw [← hamp]
        exact hX _ ⟨_, Set.mem_union_left _ ⟨_, twistedLeftOperator_mem ρ a, rfl⟩, rfl⟩
      have h3 : ∀ γ : Γ, Commute (star (twistedLeftOperator (prodCocycle σ ρ) (γ, 1))) X := fun γ ↦ by
        rw [← hshift, ← hstar]
        exact hX _ ⟨_, Set.mem_union_right _ (Set.mem_union_right _ ⟨γ, rfl⟩), rfl⟩
      have h4 : ∀ a : A, Commute (star (twistedLeftOperator (prodCocycle σ ρ) (1, a))) X := fun a ↦ by
        rw [← hamp, ← hstar, star_ampOperator]
        exact hX _ ⟨_, Set.mem_union_left _
          ⟨_, star_mem (twistedLeftOperator_mem ρ a), rfl⟩, rfl⟩
      rcases hm with ⟨⟨γ, a⟩, rfl⟩ | ⟨⟨γ, a⟩, rfl⟩
      · rw [twistedLeftOperator_prod_eq_mul σ ρ hσ hρ]
        exact (h1 γ).mul_left (h2 a)
      · show star (twistedLeftOperator (prodCocycle σ ρ) (γ, a)) * X =
          X * star (twistedLeftOperator (prodCocycle σ ρ) (γ, a))
        rw [twistedLeftOperator_prod_eq_mul σ ρ hσ hρ, star_mul]
        exact (h4 a).mul_left (h3 γ)
    · intro X hX m hm
      obtain ⟨g, hg, rfl⟩ := hm
      rcases hg with ⟨x, hx, rfl⟩ | ⟨γ, rfl⟩ | ⟨γ, rfl⟩
      · -- `x ⊗ 1` with `x ∈ L_ρ(A)`
        set Y := Φ.symm X
        have hXY : X = Φ Y := (Φ.apply_symm_apply X).symm
        have hcomm : ∀ s ∈ twistedGenerators ρ, ampOperator Γ s * Y = Y * ampOperator Γ s := by
          intro s hs
          apply Φ.injective
          rw [map_mul, map_mul, ← hXY]
          rcases hs with ⟨a, rfl⟩ | ⟨a, rfl⟩
          · rw [hamp]
            exact hX _ (Set.mem_union_left _ ⟨(1, a), rfl⟩)
          · show Φ (ampOperator Γ (star (twistedLeftOperator ρ a))) * X =
              X * Φ (ampOperator Γ (star (twistedLeftOperator ρ a)))
            rw [← star_ampOperator, hstar, hamp]
            exact hX _ (Set.mem_union_right _ ⟨(1, a), rfl⟩)
        have hentry : ∀ γ δ, entry γ δ Y ∈ Set.centralizer (twistedGenerators ρ) :=
          fun γ δ s hs ↦ entry_commute_of_commute s (hcomm s hs) γ δ
        have hxY : ampOperator Γ x * Y = Y * ampOperator Γ x :=
          commute_ampOperator_of_entry x fun γ δ ↦ (hx _ (hentry γ δ)).symm
        rw [hXY, ← map_mul, ← map_mul, hxY]
      · rw [hshift]
        exact hX _ (Set.mem_union_left _ ⟨(γ, 1), rfl⟩)
      · show Φ (star (twistedShiftOperator (H := GroupHilbert A) σ γ)) * X =
          X * Φ (star (twistedShiftOperator (H := GroupHilbert A) σ γ))
        rw [hstar, hshift]
        exact hX _ (Set.mem_union_right _ ⟨(γ, 1), rfl⟩)
  change Φ '' Set.centralizer (Set.centralizer (tensorGenerators (twistedVonNeumannAlgebra ρ) σ)) =
    Set.centralizer (Set.centralizer (twistedGenerators (prodCocycle σ ρ)))
  rw [← centralizer_image_mulEquiv, ← centralizer_image_mulEquiv, hcent]

end Conj

end

end TwistedProduct
end GroupApproximation

#audit_axioms GroupApproximation.TwistedProduct.curryConj_image_twistedTensor
