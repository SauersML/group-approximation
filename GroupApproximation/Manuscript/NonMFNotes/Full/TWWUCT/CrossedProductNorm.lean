import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.CrossedProductMatrix

/-!
# The reduced crossed product norm does not depend on the representation

Lane TWWUCT-A (work order WO-TWWUCT-A), `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (UCT input).  Brown--Ozawa, Prop. 4.1.5; Williams, Lemma 7.7.

For `x ∈ C_c(G, A)` and a finite set `F ⊆ G`, the compression
`trunc F * integrate ρ x * trunc F` is the image of the matrix
`compress x F = [s⁻¹ · x(s t⁻¹)]_{s,t ∈ F} ∈ M_F(A)` under the amplification `matRep ρ F`.
Since `matRep π F` is isometric when `π` is faithful and `⋆`-homomorphisms of
C⋆-algebras are contractive, `‖integrate ρ x‖ ≤ ‖integrate π x‖` for every
representation `ρ` and every faithful `π`; hence `‖integrate π x‖` is the same for all
faithful `π`.  We also record how `integrate` transforms along an equivariant map.
-/

namespace GroupApproximation.Full.TWWUCT.CrossedProduct

open Filter
open scoped InnerProductSpace Topology

universe u v w w'

noncomputable section

variable {G : Type u} [Group G]
variable {A : Type v} [NonUnitalCStarAlgebra A] [GCStarAlgebra G A]

/-! ## Compression of a finitely supported function to a finite set -/

/-- The matrix `[s⁻¹ · x(s t⁻¹)]_{s,t ∈ F}` of `x ∈ C_c(G, A)` over the finite set `F`. -/
def compress (x : G →₀ A) (F : Finset G) : CStarMatrix F F A :=
  CStarMatrix.ofMatrix fun (s t : F) =>
    GCStarAlgebra.act (A := A) (s : G)⁻¹ (x ((s : G) * (t : G)⁻¹))

theorem compress_apply (x : G →₀ A) (F : Finset G) (s t : F) :
    compress x F s t = GCStarAlgebra.act (A := A) (s : G)⁻¹ (x ((s : G) * (t : G)⁻¹)) :=
  rfl

theorem compress_zero (F : Finset G) : compress (0 : G →₀ A) F = 0 :=
  CStarMatrix.ext fun s t => by
    rw [compress_apply, Finsupp.zero_apply, map_zero, CStarMatrix.zero_apply]

theorem compress_add (x y : G →₀ A) (F : Finset G) :
    compress (x + y) F = compress x F + compress y F :=
  CStarMatrix.ext fun s t => by
    rw [CStarMatrix.add_apply, compress_apply, compress_apply, compress_apply,
      Finsupp.add_apply, map_add]

/-! ## Equivariant maps -/

section Comp

variable {K : Type w'} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {B : Type*} [NonUnitalCStarAlgebra B] [GCStarAlgebra G B]

theorem gen_comp (π : B →⋆ₙₐ[ℂ] (K →L[ℂ] K)) {φ : A →⋆ₙₐ[ℂ] B}
    (hφ : IsEquivariant G φ) (a : A) (g : G) : gen (π.comp φ) a g = gen π (φ a) g :=
  ContinuousLinearMap.ext fun ξ => lp.ext (funext fun s => by
    change (π.comp φ) (GCStarAlgebra.act (A := A) s⁻¹ a) (ξ (g⁻¹ * s)) =
      π (GCStarAlgebra.act (A := B) s⁻¹ (φ a)) (ξ (g⁻¹ * s))
    rw [NonUnitalStarAlgHom.comp_apply, hφ s⁻¹ a])

/-- `integrate (π ∘ φ) x = integrate π (φ ∘ x)` for an equivariant `φ`.
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (UCT input). -/
theorem integrate_comp (π : B →⋆ₙₐ[ℂ] (K →L[ℂ] K)) {φ : A →⋆ₙₐ[ℂ] B}
    (hφ : IsEquivariant G φ) (x : G →₀ A) :
    integrate (π.comp φ) x = integrate π (Finsupp.mapRange φ (map_zero φ) x) := by
  induction x using Finsupp.induction_linear with
  | zero => rw [Finsupp.mapRange_zero, map_zero, map_zero]
  | add x y hx hy =>
    rw [Finsupp.mapRange_add' (f := φ), map_add (integrate (π.comp φ)),
      map_add (integrate π), hx, hy]
  | single g a =>
    rw [Finsupp.mapRange_single, integrate_single, integrate_single, gen_comp π hφ]

end Comp

/-! ## Compressions of `integrate ρ x` -/

section Norm

variable [DecidableEq G]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type w'} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem matRep_compress_single (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (g : G) (a : A) (F : Finset G) :
    matRep ρ F (compress (Finsupp.single g a) F) = trunc F * gen ρ a g * trunc F := by
  refine ContinuousLinearMap.ext fun ξ => lp.ext (funext fun r => ?_)
  change matOp ρ F (compress (Finsupp.single g a) F) ξ r = trunc F (gen ρ a g (trunc F ξ)) r
  rw [trunc_apply_apply]
  by_cases hr : r ∈ F
  · rw [if_pos hr, matOp_apply_of_mem ρ F _ ξ hr, gen_apply, trunc_apply_apply]
    by_cases hg : g⁻¹ * r ∈ F
    · rw [if_pos hg, Finset.sum_eq_single (⟨g⁻¹ * r, hg⟩ : F)]
      · change ρ (GCStarAlgebra.act (A := A) r⁻¹ (Finsupp.single g a (r * (g⁻¹ * r)⁻¹)))
            (ξ (g⁻¹ * r)) = ρ (GCStarAlgebra.act (A := A) r⁻¹ a) (ξ (g⁻¹ * r))
        rw [mul_inv_rev, inv_inv, mul_inv_cancel_left, Finsupp.single_eq_same]
      · intro t _ ht
        have hne : r * (t : G)⁻¹ ≠ g := fun h => ht (Subtype.ext (by
          show (t : G) = g⁻¹ * r
          rw [← h, mul_inv_rev, inv_inv, inv_mul_cancel_right]))
        change ρ (GCStarAlgebra.act (A := A) r⁻¹ (Finsupp.single g a (r * (t : G)⁻¹)))
          (ξ t) = 0
        rw [Finsupp.single_eq_of_ne hne, map_zero, map_zero, ContinuousLinearMap.zero_apply]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [if_neg hg, map_zero (ρ (GCStarAlgebra.act (A := A) r⁻¹ a))]
      refine Finset.sum_eq_zero fun t _ => ?_
      have hne : r * (t : G)⁻¹ ≠ g := fun h => hg (by
        rw [← h, mul_inv_rev, inv_inv, inv_mul_cancel_right]
        exact t.2)
      change ρ (GCStarAlgebra.act (A := A) r⁻¹ (Finsupp.single g a (r * (t : G)⁻¹)))
        (ξ t) = 0
      rw [Finsupp.single_eq_of_ne hne, map_zero, map_zero, ContinuousLinearMap.zero_apply]
  · rw [if_neg hr, matOp_apply_of_notMem ρ F _ ξ hr]

/-- The compression of `integrate ρ x` to `ℓ²(F, H)` is the amplification of the matrix
`compress x F` (Brown--Ozawa, proof of Prop. 4.1.5). -/
theorem matRep_compress (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (x : G →₀ A) (F : Finset G) :
    matRep ρ F (compress x F) = trunc F * integrate ρ x * trunc F := by
  induction x using Finsupp.induction_linear with
  | zero => rw [compress_zero, map_zero, map_zero, mul_zero, zero_mul]
  | add x y hx hy =>
    rw [compress_add, map_add (matRep ρ F), hx, hy, map_add (integrate ρ), mul_add, add_mul]
  | single g a => rw [matRep_compress_single, integrate_single]

omit [Group G] [CompleteSpace H] in
/-- An operator on `ℓ²(G, H)` whose compressions to all finite sets are bounded by `c`
is bounded by `c`. -/
theorem norm_le_of_trunc (T : L2 G H →L[ℂ] L2 G H) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ F : Finset G, ‖trunc F * T * trunc F‖ ≤ c) : ‖T‖ ≤ c := by
  refine ContinuousLinearMap.opNorm_le_bound T hc fun ξ => ?_
  have h1 : Tendsto (fun F : Finset G => ‖trunc F ξ - ξ‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_trunc ξ)
  have h2 : Tendsto (fun F : Finset G => ‖T‖ * ‖trunc F ξ - ξ‖) atTop (𝓝 0) := by
    have h3 := h1.const_mul ‖T‖
    rwa [mul_zero] at h3
  have hlim : Tendsto (fun F : Finset G => trunc F (T (trunc F ξ))) atTop (𝓝 (T ξ)) := by
    refine (tendsto_trunc (T ξ)).congr_dist
      (squeeze_zero (fun _ => dist_nonneg) (fun F => ?_) h2)
    show dist (trunc F (T ξ)) (trunc F (T (trunc F ξ))) ≤ ‖T‖ * ‖trunc F ξ - ξ‖
    rw [dist_eq_norm, ← map_sub (trunc (H := H) F), ← map_sub T]
    calc ‖trunc F (T (ξ - trunc F ξ))‖ ≤ ‖T (ξ - trunc F ξ)‖ := norm_trunc_apply_le F _
      _ ≤ ‖T‖ * ‖ξ - trunc F ξ‖ := T.le_opNorm _
      _ = ‖T‖ * ‖trunc F ξ - ξ‖ := by rw [norm_sub_rev]
  refine le_of_tendsto hlim.norm (Eventually.of_forall fun F => ?_)
  calc ‖trunc F (T (trunc F ξ))‖ = ‖(trunc F * T * trunc F) ξ‖ := rfl
    _ ≤ ‖trunc F * T * trunc F‖ * ‖ξ‖ := (trunc F * T * trunc F).le_opNorm ξ
    _ ≤ c * ‖ξ‖ := mul_le_mul_of_nonneg_right (h F) (norm_nonneg ξ)

theorem norm_trunc_mul_integrate_le (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    {π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)} (hπ : Function.Injective π) (x : G →₀ A) (F : Finset G) :
    ‖trunc F * integrate ρ x * trunc F‖ ≤ ‖integrate π x‖ := by
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  rw [← matRep_compress ρ x F]
  calc ‖matRep ρ F (compress x F)‖ ≤ ‖compress x F‖ :=
        NonUnitalStarAlgHom.norm_apply_le (matRep ρ F) (compress x F)
    _ = ‖matRep π F (compress x F)‖ :=
        (NonUnitalStarAlgHom.norm_map (matRep π F) (matRep_injective hπ F) (compress x F)).symm
    _ = ‖trunc F * integrate π x * trunc F‖ := by rw [matRep_compress]
    _ ≤ ‖trunc F * integrate π x‖ * ‖trunc (H := K) F‖ := norm_mul_le _ _
    _ ≤ ‖trunc F * integrate π x‖ := mul_le_of_le_one_right (norm_nonneg _) (norm_trunc_le F)
    _ ≤ ‖trunc (H := K) F‖ * ‖integrate π x‖ := norm_mul_le _ _
    _ ≤ ‖integrate π x‖ := mul_le_of_le_one_left (norm_nonneg _) (norm_trunc_le F)

omit [DecidableEq G] in
/-- **Representation independence, one inequality** (Brown--Ozawa, Prop. 4.1.5):
`‖∑ ρ̃(x_g) λ_g‖ ≤ ‖∑ π̃(x_g) λ_g‖` for any representation `ρ` and faithful `π`.
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (UCT input). -/
theorem norm_integrate_le (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) {π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)}
    (hπ : Function.Injective π) (x : G →₀ A) : ‖integrate ρ x‖ ≤ ‖integrate π x‖ := by
  classical
  exact norm_le_of_trunc (integrate ρ x) (norm_nonneg _) (norm_trunc_mul_integrate_le ρ hπ x)

omit [DecidableEq G] in
/-- **Representation independence of the reduced norm** (Brown--Ozawa, Prop. 4.1.5;
Williams, Lemma 7.7).  `non_mf_group_notes.tex`, `thm:fixed-radical-membership`
(UCT input). -/
theorem norm_integrate_eq {ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} {π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)}
    (hρ : Function.Injective ρ) (hπ : Function.Injective π) (x : G →₀ A) :
    ‖integrate ρ x‖ = ‖integrate π x‖ :=
  le_antisymm (norm_integrate_le ρ hπ x) (norm_integrate_le π hρ x)

end Norm

end

end GroupApproximation.Full.TWWUCT.CrossedProduct
