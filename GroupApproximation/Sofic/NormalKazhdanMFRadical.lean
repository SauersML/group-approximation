import GroupApproximation.Sofic.KazhdanCompressionFunctorial
import GroupApproximation.Sofic.NormalKazhdanCompressionObstruction
import GroupApproximation.Sofic.OperatorMFLocalNormalization
import GroupApproximation.Sofic.NormMFResidualExactQuotient
import GroupApproximation.Analysis.NormMatrixCoronaUnitary

/-!
# Normal Kazhdan subgroups lie in the operator-MF residual

The normal-Kazhdan compression obstruction can be applied inside the range
of an arbitrary homomorphism to a norm-matrix ultraproduct.  If an element of
the Kazhdan subgroup survived, its image subgroup would still be normal,
Kazhdan, nontrivial, and contained in the mapped compression defect.

The ambient range is countable and embeds in that same ultraproduct.  Its
universal norm-MF residual is therefore trivial, so it is operator-MF.  Local
tensor-power normalization turns this into a weak-MF approximation, contrary
to the normal-Kazhdan compression obstruction.
-/

namespace GroupApproximation

universe u v

/-- Every finite group has property `(T)`: the whole group together with
tolerance `1` is a Kazhdan pair, because summing the orbit of an
almost-invariant unit vector produces a nonzero invariant vector.  This makes
the finite-normal obstruction literally the finite case of the
normal-Kazhdan obstruction below. -/
theorem hasKazhdanPropertyT_of_finite :
    ∀ (G : Type u) [Group G] [Finite G], HasKazhdanPropertyT.{u, v} G := by
  intro G _ _
  classical
  letI : Fintype G := Fintype.ofFinite G
  refine ⟨Finset.univ, 1, one_pos, ?_⟩
  intro E _ _ _ ρ x hx hmove
  refine ⟨∑ g : G, ρ g x, ?_, ?_⟩
  · intro hzero
    have hrw : (∑ g : G, ρ g x) - (Fintype.card G : ℝ) • x
        = ∑ g : G, (ρ g x - x) := by
      rw [Finset.sum_sub_distrib]
      congr 1
      rw [Finset.sum_const, Finset.card_univ]
      exact Nat.cast_smul_eq_nsmul ℝ _ x
    have hbound : ‖(∑ g : G, ρ g x) - (Fintype.card G : ℝ) • x‖
        < Fintype.card G := by
      rw [hrw]
      calc ‖∑ g : G, (ρ g x - x)‖
          ≤ ∑ g : G, ‖ρ g x - x‖ := norm_sum_le _ _
        _ < ∑ _g : G, (1 : ℝ) :=
            Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
              (fun g _ ↦ hmove g (Finset.mem_univ g))
        _ = Fintype.card G := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [hzero, zero_sub, norm_neg, norm_smul, hx] at hbound
    simp only [Real.norm_natCast, mul_one] at hbound
    exact absurd hbound (lt_irrefl _)
  · intro h
    have happ : ρ h (∑ g : G, ρ g x) = ∑ g : G, ρ (h * g) x := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun g _ ↦ ?_
      have := DFunLike.congr_fun (map_mul ρ h g) x
      exact this.symm
    rw [happ]
    exact Fintype.sum_equiv (Equiv.mulLeft h)
      (fun g ↦ ρ (h * g) x) (fun g ↦ ρ g x) (fun g ↦ rfl)

namespace KazhdanCompressionCore

variable {Γ E : Type} [Group Γ] [Group E]

/-- A normal property-`(T)` subgroup contained in the compression defect is
killed elementwise by every operator-norm matrix-ultraproduct
representation.  Finiteness, centrality, and torsion are unnecessary. -/
theorem normalKazhdan_le_normMFResidual
    [Countable E] (C : KazhdanCompressionCore Γ E)
    (K : Subgroup E) [K.Normal]
    (hT : HasKazhdanPropertyT.{0, 0} K)
    (hK : K ≤ C.defectNormal) :
    K ≤ normMFResidual E := by
  intro k hk
  rw [mem_normMFResidual_iff]
  intro I U X rho
  by_contra hsurvive
  let f : E →* rho.range := rho.rangeRestrict
  let K' : Subgroup rho.range := K.map f
  letI : Countable rho.range :=
    Function.Surjective.countable rho.rangeRestrict_surjective
  letI : K'.Normal :=
    map_subgroup_normal K f rho.rangeRestrict_surjective
  have hT' : HasKazhdanPropertyT.{0, 0} K' :=
    map_subgroup_hasKazhdanPropertyT K f hT
  have hk' : f k ∈ K' := ⟨k, hk, rfl⟩
  have hfk_ne : f k ≠ 1 := by
    intro heq
    apply hsurvive
    exact congrArg Subtype.val heq
  letI : Nontrivial K' :=
    ⟨⟨⟨f k, hk'⟩, 1, fun heq ↦ hfk_ne (congrArg Subtype.val heq)⟩⟩
  have hres : normMFResidual rho.range = ⊥ := by
    apply Subgroup.eq_bot_iff_forall (normMFResidual rho.range) |>.2
    intro y hy
    apply Subtype.ext
    exact map_eq_one_of_mem_normMFResidual U X rho.range.subtype hy
  have hRangeOperatorMF : IsOperatorMF rho.range :=
    isOperatorMF_of_normMFResidual_eq_bot hres
  have hRangeWeakMF : IsWeakMF rho.range :=
    ⟨1, by norm_num,
      OperatorMFLocalNormalization.isNormApproximable_one hRangeOperatorMF⟩
  exact (C.map f).not_isWeakMF_of_normalKazhdan_le_defect
    K' hT' (C.map_subgroup_le_defectNormal f K hK) hRangeWeakMF

/-- A normal Kazhdan subgroup contained in the compression defect lies in
the universal cofinite norm-matrix-corona residual.  This is the same
unconditional obstruction as `normalKazhdan_le_normMFResidual`, expressed in
the manuscript's concrete corona target language. -/
theorem normalKazhdan_le_coronaMFResidual
    [Countable E] (C : KazhdanCompressionCore Γ E)
    (K : Subgroup E) [K.Normal]
    (hT : HasKazhdanPropertyT.{0, 0} K)
    (hK : K ≤ C.defectNormal) :
    K ≤ coronaMFResidual E := by
  rw [coronaMFResidual_eq_normMFResidual]
  exact C.normalKazhdan_le_normMFResidual K hT hK

/-- A normal Kazhdan subgroup in the compression defect is killed by every
homomorphism into the unitary group of a genuine norm-matrix C-star quotient. -/
theorem normalKazhdan_le_normMatrixCStarCoronaKernel
    [Countable E] (C : KazhdanCompressionCore Γ E)
    (K : Subgroup E) [K.Normal]
    (hT : HasKazhdanPropertyT.{0, 0} K)
    (hK : K ≤ C.defectNormal)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)) :
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    ∀ rho : E →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
      K ≤ rho.ker := by
  letI : ∀ n, Nonempty (X n) :=
    fun n ↦ Fintype.card_pos_iff.mp (hX n)
  intro rho
  let sigma : E →* NormMatrixCoronaUnitary X :=
    (normMatrixCoronaUnitaryEquiv X).symm.toMonoidHom.comp rho
  intro k hk
  have hres : k ∈ normMFResidual E :=
    C.normalKazhdan_le_normMFResidual K hT hK hk
  have hkernel : k ∈ sigma.ker :=
    NormMFInvisible.toCoronaMFInvisible
      (mem_normMFResidual_iff.mp hres) X hX sigma
  apply MonoidHom.mem_ker.mpr
  apply (normMatrixCoronaUnitaryEquiv X).symm.injective
  simpa [sigma] using MonoidHom.mem_ker.mp hkernel

/-- The subgroup generated by all normal Kazhdan subgroups contained in the
compression defect. -/
def normalKazhdanDefectPart (C : KazhdanCompressionCore Γ E) : Subgroup E :=
  sSup {K : Subgroup E |
    K.Normal ∧ HasKazhdanPropertyT.{0, 0} K ∧ K ≤ C.defectNormal}

/-- Even when the whole compression defect is not Kazhdan, the subgroup
generated by all of its normal Kazhdan subgroups lies in the MF residual. -/
theorem normalKazhdanDefectPart_le_normMFResidual
    [Countable E] (C : KazhdanCompressionCore Γ E) :
    C.normalKazhdanDefectPart ≤ normMFResidual E := by
  apply sSup_le
  intro K hK
  letI : K.Normal := hK.1
  exact C.normalKazhdan_le_normMFResidual K hK.2.1 hK.2.2

/-- If the entire compression defect has property `(T)`, every norm-matrix
corona representation factors through the quotient by that defect. -/
theorem existsUnique_defectNormal_factorization_to_normMatrixCorona
    [Countable E] (C : KazhdanCompressionCore Γ E)
    (hT : HasKazhdanPropertyT.{0, 0} C.defectNormal)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n))
    (rho : E →* NormMatrixCoronaUnitary X) :
    ∃! rhoBar : (E ⧸ C.defectNormal) →* NormMatrixCoronaUnitary X,
      rhoBar.comp (QuotientGroup.mk' C.defectNormal) = rho := by
  refine existsUnique_quotient_factorization_to_normMatrixCorona
    C.defectNormal ?_ X hX rho
  rw [coronaMFResidual_eq_normMFResidual]
  exact C.normalKazhdan_le_normMFResidual C.defectNormal hT le_rfl

/-- If the full compression defect has property `(T)`, every homomorphism
into a genuine norm-matrix C-star-corona unitary group factors uniquely
through the quotient by that defect. -/
theorem existsUnique_defectNormal_factorization_to_normMatrixCStarCorona
    [Countable E] (C : KazhdanCompressionCore Γ E)
    (hT : HasKazhdanPropertyT.{0, 0} C.defectNormal)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)) :
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    ∀ rho : E →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
      ∃! rhoBar : ((E ⧸ C.defectNormal) →*
          unitary (NormMatrixCStarCorona (fun n ↦ X n))),
        rhoBar.comp (QuotientGroup.mk' C.defectNormal) = rho := by
  letI : ∀ n, Nonempty (X n) :=
    fun n ↦ Fintype.card_pos_iff.mp (hX n)
  intro rho
  have hker : C.defectNormal ≤ rho.ker :=
    C.normalKazhdan_le_normMatrixCStarCoronaKernel C.defectNormal hT le_rfl X hX rho
  let rhoBar := QuotientGroup.lift C.defectNormal rho hker
  have hcomp : rhoBar.comp (QuotientGroup.mk' C.defectNormal) = rho :=
    QuotientGroup.lift_comp_mk' C.defectNormal rho hker
  refine ⟨rhoBar, hcomp, ?_⟩
  intro f hf
  apply MonoidHom.ext
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective C.defectNormal q
  exact DFunLike.congr_fun (hf.trans hcomp.symm) g

/-- If the full defect is Kazhdan and its quotient is operator-MF, then the
defect is exactly the MF residual, so the quotient is the largest MF
quotient. -/
theorem normMFResidual_eq_defectNormal
    [Countable E] (C : KazhdanCompressionCore Γ E)
    (hT : HasKazhdanPropertyT.{0, 0} C.defectNormal)
    (hquot : IsOperatorMF (E ⧸ C.defectNormal)) :
    normMFResidual E = C.defectNormal :=
  normMFResidual_eq_of_le_and_quotient_isOperatorMF C.defectNormal
    (C.normalKazhdan_le_normMFResidual C.defectNormal hT le_rfl) hquot

end KazhdanCompressionCore
end GroupApproximation
