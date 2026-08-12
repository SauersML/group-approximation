import GroupApproximation.Sofic.WeakMFUltraproduct
import GroupApproximation.Sofic.LEFSofic

/-!
# Weak-MF transfer along group embeddings

Operator-norm matrix approximation is inherited by subgroups.  This elementary
fact is the last purely local step in the weak-MF amalgamation argument: once
an analytic construction embeds a group into an MF unitary group, the source
itself is weak-MF.

The proof below works directly with finite `NormModel`s.  It does not use an
ultraproduct, a trace, or any permanence theorem for C*-algebras.
-/

namespace GroupApproximation

open Matrix
open scoped Matrix.Norms.L2Operator

universe u v

variable {H : Type u} {G : Type v} [Group H] [Group G]

/-- Pull an operator-norm model back along an injective group homomorphism. -/
noncomputable def NormModel.comap (ι : H →* G) (hι : Function.Injective ι)
    {F : Finset H} {E : Finset G} {δ ε : ℝ}
    (hF : ∀ h ∈ F, ι h ∈ E) (M : NormModel G E δ ε) : NormModel H F δ ε := by
  classical
  exact {
    carrier := M.carrier
    nonempty := M.nonempty
    map h := M.map (ι h)
    isUnitary h := M.isUnitary (ι h)
    multiplicative := by
      intro g hg h hh
      simpa only [map_mul] using
        M.multiplicative (ι g) (hF g hg) (ι h) (hF h hh)
    separated := by
      intro g hg h hh hne
      exact M.separated (ι g) (hF g hg) (ι h) (hF h hh) (hι.ne hne) }

/-- Operator-norm approximability is inherited through an injective group
homomorphism. -/
theorem isNormApproximable_of_injective (ι : H →* G)
    (hι : Function.Injective ι) {δ : ℝ}
    (hG : IsNormApproximable G δ) : IsNormApproximable H δ := by
  classical
  intro F ε hε
  obtain ⟨M⟩ := hG (F.image ι) ε hε
  exact ⟨M.comap ι hι (fun h hh ↦ Finset.mem_image.mpr ⟨h, hh, rfl⟩)⟩

/-- **Weak-MF passes to subgroups.** -/
theorem isWeakMF_of_injective (ι : H →* G) (hι : Function.Injective ι)
    (hG : IsWeakMF G) : IsWeakMF H := by
  obtain ⟨δ, hδ, happrox⟩ := hG
  exact ⟨δ, hδ, isNormApproximable_of_injective ι hι happrox⟩

/-! ## Exact finite models -/

/-- A local embedding into finite permutation groups is already an
operator-norm model: multiplicativity is exact, and two distinct permutation
matrices are at operator-norm distance at least `1`. -/
theorem isNormApproximable_of_isLEF (hLEF : IsLEF H) :
    IsNormApproximable H 1 := by
  classical
  intro F ε hε
  obtain ⟨n, f, hinj, hmul⟩ := hLEF F
  let Q := Equiv.Perm (Fin n)
  set Y : FiniteModel := ⟨Q, inferInstance, inferInstance⟩ with hY
  refine ⟨{
    carrier := Y
    nonempty := Fintype.card_pos_iff.mpr ⟨1⟩
    map := fun g ↦ ((MulAction.toPermHom Q Q (f g))⁻¹).permMatrix ℂ
    isUnitary := fun g ↦ permMatrix_mem_unitaryGroup Y _
    multiplicative := ?_
    separated := ?_ }⟩
  · intro g hg k hk
    have hlocal : f (g * k) = f g * f k := hmul.map_mul g hg k hk
    have hmatrix :
        ((MulAction.toPermHom Q Q (f g))⁻¹).permMatrix ℂ
          * ((MulAction.toPermHom Q Q (f k))⁻¹).permMatrix ℂ
        = ((MulAction.toPermHom Q Q (f (g * k)))⁻¹).permMatrix ℂ := by
      rw [hlocal, map_mul, _root_.mul_inv_rev, Matrix.permMatrix_mul]
    rw [hmatrix, sub_self, norm_zero]
    exact hε.le
  · intro g hg k hk hne
    have hperm : f g ≠ f k := by
      intro heq
      exact hne (hinj (Finset.mem_coe.mpr hg) (Finset.mem_coe.mpr hk) heq)
    have hg1 : (MulAction.toPermHom Q Q (f g))⁻¹ (1 : Q) = (f g)⁻¹ := by
      simp [MulAction.toPermHom]
    have hk1 : ¬ (MulAction.toPermHom Q Q (f k))⁻¹ (1 : Q) = (f g)⁻¹ := by
      have : (MulAction.toPermHom Q Q (f k))⁻¹ (1 : Q) = (f k)⁻¹ := by
        simp [MulAction.toPermHom]
      rw [this]
      exact fun heq ↦ hperm (inv_injective heq).symm
    have hPent := permMatrixC_entry Y (MulAction.toPermHom Q Q (f g))⁻¹
      (1 : Q) (f g)⁻¹
    have hQent := permMatrixC_entry Y (MulAction.toPermHom Q Q (f k))⁻¹
      (1 : Q) (f g)⁻¹
    rw [if_pos hg1] at hPent
    rw [if_neg hk1] at hQent
    have hentry : Complex.normSq
        ((((MulAction.toPermHom Q Q (f g))⁻¹).permMatrix ℂ
          - ((MulAction.toPermHom Q Q (f k))⁻¹).permMatrix ℂ)
          (1 : Q) (f g)⁻¹) = 1 := by
      rw [Matrix.sub_apply, hPent, hQent, sub_zero]
      simp
    have hbound := normSq_entry_le_sq_l2_opNorm Y
      (((MulAction.toPermHom Q Q (f g))⁻¹).permMatrix ℂ
        - ((MulAction.toPermHom Q Q (f k))⁻¹).permMatrix ℂ)
      (1 : Q) (f g)⁻¹
    rw [hentry] at hbound
    nlinarith [norm_nonneg
      (((MulAction.toPermHom Q Q (f g))⁻¹).permMatrix ℂ
        - ((MulAction.toPermHom Q Q (f k))⁻¹).permMatrix ℂ)]

/-- **LEF groups are weak-MF.**  In particular, residually finite groups
have exact operator-norm local models. -/
theorem isWeakMF_of_isLEF (hLEF : IsLEF H) : IsWeakMF H :=
  ⟨1, by norm_num, isNormApproximable_of_isLEF hLEF⟩

/-- **Residually finite groups are weak-MF.** -/
theorem isWeakMF_of_residuallyFinite [Group.ResiduallyFinite H] : IsWeakMF H :=
  isWeakMF_of_isLEF isLEF_of_residuallyFinite

end GroupApproximation
