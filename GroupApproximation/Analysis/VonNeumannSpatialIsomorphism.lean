import GroupApproximation.Analysis.TwistedTensorProductAlgebra
import GroupApproximation.Meta.AxiomGuard

/-!
# Spatial isomorphisms of von Neumann algebras

Infrastructure of lane `oa-mcduff` for `simple_kazhdan_sofic_group.tex` at origin/main 37551fd93,
"Brown's formulation", tex 280–283 (census row `97438886a277`): "`L(G) ⊗̄ 𝓡` is a McDuff factor", i.e.
`L(G) ⊗̄ 𝓡 ≅ (L(G) ⊗̄ 𝓡) ⊗̄ 𝓡`.  The isomorphism is a chain of spatial isomorphisms `Ad U`; this
module supplies the three kinds of links.

* `restrictConj`: `Ad U` with `Ad U '' M = N` restricts to a ⋆-algebra isomorphism `M ≃ N`.
* `vecMap U`: `1 ⊗ U` on `ℓ²(Γ; ·)`; `conj_image_twistedTensor`: if `Ad U '' M = N` then
  `Ad (U ⊗ 1) '' (M ⊗̄ L_σ(Γ)) = N ⊗̄ L_σ(Γ)`.
* `conj_image_twistedVonNeumannAlgebra_of_mulEquiv`: a group isomorphism `φ : A ≃ B` carrying the cocycle
  `σ_A` to `σ_B` reindexes `L_{σ_A}(A)` onto `L_{σ_B}(B)`.
-/

namespace GroupApproximation
namespace SpatialIso

open ReducedGroupCStarTrace TwistedGroupVonNeumann TwistedTensor TwistedProduct
open scoped InnerProductSpace

noncomputable section

universe u v w

/-! ## Restricting `Ad U` -/

section Restrict

variable {H : Type u} {K : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem conj_mem {U : H ≃ₗᵢ[ℂ] K} {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
    (hMN : U.conjStarAlgEquiv '' (M : Set (H →L[ℂ] H)) = (N : Set (K →L[ℂ] K)))
    {T : H →L[ℂ] H} (hT : T ∈ M) : U.conjStarAlgEquiv T ∈ N := by
  have h : U.conjStarAlgEquiv T ∈ (N : Set (K →L[ℂ] K)) := hMN ▸ ⟨T, hT, rfl⟩
  exact h

theorem conj_symm_mem {U : H ≃ₗᵢ[ℂ] K} {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
    (hMN : U.conjStarAlgEquiv '' (M : Set (H →L[ℂ] H)) = (N : Set (K →L[ℂ] K)))
    {S : K →L[ℂ] K} (hS : S ∈ N) : U.conjStarAlgEquiv.symm S ∈ M := by
  have h : S ∈ U.conjStarAlgEquiv '' (M : Set (H →L[ℂ] H)) := hMN.symm ▸ hS
  obtain ⟨T, hT, rfl⟩ := h
  rwa [StarAlgEquiv.symm_apply_apply]

/-- **`Ad U` restricts to a ⋆-algebra isomorphism** `M ≃ N` when it carries `M` onto `N`. -/
def restrictConj (U : H ≃ₗᵢ[ℂ] K) {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
    (hMN : U.conjStarAlgEquiv '' (M : Set (H →L[ℂ] H)) = (N : Set (K →L[ℂ] K))) :
    ↥M.toStarSubalgebra ≃⋆ₐ[ℂ] ↥N.toStarSubalgebra where
  toFun T := ⟨U.conjStarAlgEquiv T, conj_mem hMN T.2⟩
  invFun S := ⟨U.conjStarAlgEquiv.symm S, conj_symm_mem hMN S.2⟩
  left_inv T := Subtype.ext (StarAlgEquiv.symm_apply_apply _ (T : H →L[ℂ] H))
  right_inv S := Subtype.ext (StarAlgEquiv.apply_symm_apply _ (S : K →L[ℂ] K))
  map_mul' T S := Subtype.ext (map_mul U.conjStarAlgEquiv (T : H →L[ℂ] H) S)
  map_add' T S := Subtype.ext (map_add U.conjStarAlgEquiv (T : H →L[ℂ] H) S)
  map_star' T := Subtype.ext (map_star U.conjStarAlgEquiv (T : H →L[ℂ] H))
  map_smul' c T := Subtype.ext (map_smul U.conjStarAlgEquiv c (T : H →L[ℂ] H))

end Restrict

/-! ## `1 ⊗ U` on `ℓ²(Γ; ·)` -/

section VecMap

variable {H : Type u} {K : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] {Γ : Type w}

theorem memℓp_vecMap (U : H ≃ₗᵢ[ℂ] K) (f : VecHilbert Γ H) : Memℓp (fun γ : Γ ↦ U (f γ)) 2 := by
  apply memℓp_gen
  have h := (memℓp_gen_iff (by norm_num)).1 (lp.memℓp f)
  simpa only [LinearIsometryEquiv.norm_map] using h

/-- `1 ⊗ U` as a linear equivalence `ℓ²(Γ; H) ≃ ℓ²(Γ; K)`. -/
def vecMapLinear (U : H ≃ₗᵢ[ℂ] K) : VecHilbert Γ H ≃ₗ[ℂ] VecHilbert Γ K where
  toFun f := ⟨fun γ ↦ U (f γ), memℓp_vecMap U f⟩
  invFun g := ⟨fun γ ↦ U.symm (g γ), memℓp_vecMap U.symm g⟩
  map_add' f g := by
    apply lp.ext
    funext γ
    change U ((⇑(f + g)) γ) = U (f γ) + U (g γ)
    rw [lp.coeFn_add, Pi.add_apply, map_add]
  map_smul' c f := by
    apply lp.ext
    funext γ
    change U ((⇑(c • f)) γ) = c • U (f γ)
    rw [lp.coeFn_smul, Pi.smul_apply, map_smul]
  left_inv f := by
    apply lp.ext
    funext γ
    exact U.symm_apply_apply (f γ)
  right_inv g := by
    apply lp.ext
    funext γ
    exact U.apply_symm_apply (g γ)

/-- `1 ⊗ U` is unitary. -/
def vecMap (U : H ≃ₗᵢ[ℂ] K) : VecHilbert Γ H ≃ₗᵢ[ℂ] VecHilbert Γ K :=
  (vecMapLinear U).isometryOfInner (by
    intro f g
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    exact tsum_congr fun γ ↦ U.inner_map_map (f γ) (g γ))

@[simp]
theorem vecMap_apply (U : H ≃ₗᵢ[ℂ] K) (f : VecHilbert Γ H) (γ : Γ) : vecMap U f γ = U (f γ) :=
  rfl

theorem vecMap_symm_apply (U : H ≃ₗᵢ[ℂ] K) (g : VecHilbert Γ K) (γ : Γ) :
    (vecMap U).symm g γ = U.symm (g γ) :=
  rfl

theorem conj_vecMap_ampOperator (U : H ≃ₗᵢ[ℂ] K) (x : H →L[ℂ] H) :
    (vecMap (Γ := Γ) U).conjStarAlgEquiv (ampOperator Γ x) = ampOperator Γ (U.conjStarAlgEquiv x) := by
  apply ContinuousLinearMap.ext
  intro g
  rfl

theorem conj_vecMap_twistedShiftOperator [Group Γ] (U : H ≃ₗᵢ[ℂ] K) (σ : Γ → Γ → ZMod 2) (γ : Γ) :
    (vecMap (Γ := Γ) U).conjStarAlgEquiv (twistedShiftOperator (H := H) σ γ) =
      twistedShiftOperator (H := K) σ γ := by
  apply ContinuousLinearMap.ext
  intro g
  apply lp.ext
  funext δ
  show U (zsign (σ γ (γ⁻¹ * δ)) • U.symm (g (γ⁻¹ * δ))) = zsign (σ γ (γ⁻¹ * δ)) • g (γ⁻¹ * δ)
  rw [map_smul, U.apply_symm_apply]

/-- **Functoriality of `⊗̄ L_σ(Γ)`** under spatial isomorphisms. -/
theorem conj_image_twistedTensor [Group Γ] (U : H ≃ₗᵢ[ℂ] K) {M : VonNeumannAlgebra H}
    {N : VonNeumannAlgebra K}
    (hMN : U.conjStarAlgEquiv '' (M : Set (H →L[ℂ] H)) = (N : Set (K →L[ℂ] K)))
    (σ : Γ → Γ → ZMod 2) :
    (vecMap (Γ := Γ) U).conjStarAlgEquiv '' (twistedTensor M σ : Set (VecHilbert Γ H →L[ℂ] VecHilbert Γ H)) =
      (twistedTensor N σ : Set (VecHilbert Γ K →L[ℂ] VecHilbert Γ K)) := by
  let Φ := ((vecMap (Γ := Γ) U).conjStarAlgEquiv).toMulEquiv
  have hgen : Φ '' tensorGenerators M σ = tensorGenerators N σ := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      rcases hg with ⟨x, hx, rfl⟩ | ⟨γ, rfl⟩ | ⟨γ, rfl⟩
      · exact Set.mem_union_left _ ⟨_, conj_mem hMN hx, (conj_vecMap_ampOperator U x).symm⟩
      · exact Set.mem_union_right _ (Set.mem_union_left _ ⟨γ, (conj_vecMap_twistedShiftOperator U σ γ).symm⟩)
      · refine Set.mem_union_right _ (Set.mem_union_right _ ⟨γ, ?_⟩)
        change star (twistedShiftOperator σ γ) =
          (vecMap (Γ := Γ) U).conjStarAlgEquiv (star (twistedShiftOperator σ γ))
        rw [map_star, conj_vecMap_twistedShiftOperator]
    · rintro (⟨x, hx, rfl⟩ | ⟨γ, rfl⟩ | ⟨γ, rfl⟩)
      · obtain ⟨T, hT, rfl⟩ : x ∈ U.conjStarAlgEquiv '' (M : Set (H →L[ℂ] H)) := hMN.symm ▸ hx
        exact ⟨ampOperator Γ T, Set.mem_union_left _ ⟨T, hT, rfl⟩, conj_vecMap_ampOperator U T⟩
      · exact ⟨twistedShiftOperator σ γ, Set.mem_union_right _ (Set.mem_union_left _ ⟨γ, rfl⟩),
          conj_vecMap_twistedShiftOperator U σ γ⟩
      · refine ⟨star (twistedShiftOperator σ γ),
          Set.mem_union_right _ (Set.mem_union_right _ ⟨γ, rfl⟩), ?_⟩
        change (vecMap (Γ := Γ) U).conjStarAlgEquiv (star (twistedShiftOperator σ γ)) = _
        rw [map_star, conj_vecMap_twistedShiftOperator]
  change Φ '' Set.centralizer (Set.centralizer (tensorGenerators M σ)) =
    Set.centralizer (Set.centralizer (tensorGenerators N σ))
  rw [← centralizer_image_mulEquiv, ← centralizer_image_mulEquiv, hgen]

end VecMap

/-! ## Reindexing along cocycle-preserving group isomorphisms -/

section Reindex

variable {A B : Type u} [Group A] [Group B]

/-- **A cocycle-preserving group isomorphism reindexes twisted group von Neumann algebras.** -/
theorem conj_image_twistedVonNeumannAlgebra_of_mulEquiv (φ : A ≃* B) (σA : A → A → ZMod 2)
    (σB : B → B → ZMod 2) (hφ : ∀ x y, σB (φ x) (φ y) = σA x y) :
    (lpCongrLeft φ.toEquiv).conjStarAlgEquiv ''
        (twistedVonNeumannAlgebra σA : Set (GroupHilbert A →L[ℂ] GroupHilbert A)) =
      (twistedVonNeumannAlgebra σB : Set (GroupHilbert B →L[ℂ] GroupHilbert B)) := by
  let Φ := ((lpCongrLeft φ.toEquiv).conjStarAlgEquiv).toMulEquiv
  have hop : ∀ x : A, (lpCongrLeft φ.toEquiv).conjStarAlgEquiv (twistedLeftOperator σA x) =
      twistedLeftOperator σB (φ x) := by
    intro x
    apply ContinuousLinearMap.ext
    intro F
    apply lp.ext
    funext h
    show zsign (σA x (x⁻¹ * φ.symm h)) * F (φ (x⁻¹ * φ.symm h)) =
      zsign (σB (φ x) ((φ x)⁻¹ * h)) * F ((φ x)⁻¹ * h)
    have hh : φ (x⁻¹ * φ.symm h) = (φ x)⁻¹ * h := by
      rw [map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [hh, ← hφ, hh]
  have hgen : Φ '' twistedGenerators σA = twistedGenerators σB := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      rcases hg with ⟨x, rfl⟩ | ⟨x, rfl⟩
      · exact Set.mem_union_left _ ⟨φ x, (hop x).symm⟩
      · refine Set.mem_union_right _ ⟨φ x, ?_⟩
        change star (twistedLeftOperator σB (φ x)) =
          (lpCongrLeft φ.toEquiv).conjStarAlgEquiv (star (twistedLeftOperator σA x))
        rw [map_star, hop]
    · rintro (⟨b, rfl⟩ | ⟨b, rfl⟩)
      · refine ⟨twistedLeftOperator σA (φ.symm b), Set.mem_union_left _ ⟨_, rfl⟩, ?_⟩
        change (lpCongrLeft φ.toEquiv).conjStarAlgEquiv (twistedLeftOperator σA (φ.symm b)) = _
        rw [hop, MulEquiv.apply_symm_apply]
      · refine ⟨star (twistedLeftOperator σA (φ.symm b)), Set.mem_union_right _ ⟨_, rfl⟩, ?_⟩
        change (lpCongrLeft φ.toEquiv).conjStarAlgEquiv (star (twistedLeftOperator σA (φ.symm b))) = _
        rw [map_star, hop, MulEquiv.apply_symm_apply]
  change Φ '' Set.centralizer (Set.centralizer (twistedGenerators σA)) =
    Set.centralizer (Set.centralizer (twistedGenerators σB))
  rw [← centralizer_image_mulEquiv, ← centralizer_image_mulEquiv, hgen]

end Reindex

end

end SpatialIso
end GroupApproximation

#audit_axioms GroupApproximation.SpatialIso.conj_image_twistedTensor
#audit_axioms GroupApproximation.SpatialIso.conj_image_twistedVonNeumannAlgebra_of_mulEquiv
