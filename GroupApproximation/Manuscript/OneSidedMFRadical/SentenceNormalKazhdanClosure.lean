import GroupApproximation.Manuscript.OneSidedMFRadical.NormalKazhdan

/-!
# Sentence closure for the normal-Kazhdan MF-radical proof

The printed proof now follows the already formalized moving-corner/`WeakMF`
argument.  This file gives a named theorem to every mathematical sentence in
that proof.  In particular, none of these declarations mentions a maximal
group C-star algebra or imports a Kazhdan projection from the literature.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter

/-- Membership in the operator-to-Hilbert--Schmidt shadow residual is exactly
the coordinatewise killing hypothesis used by the moving-corner theorem. -/
theorem manuscriptNormalKazhdanShadowKill
    (G : Type) [Group G] (D K : Subgroup G)
    (hD : D ≤ opToHSShadowResidual G) (hK : K ≤ D) :
    ∀ (B : OpAlmostRepresentation G) (U : Ultrafilter ℕ)
      (hcof : (U : Filter ℕ) ≤ Filter.cofinite) (x : K),
      (KazhdanCompressionCore.toAsymptoticUnitaryRepresentation B).toUltraproductHom
        hcof (x : G) = 1 := by
  intro B U hcof x
  exact (mem_opToHSShadowResidual_iff (x : G)).mp
    (hD (hK x.property)) B U hcof

/-- The exact moving-corner engine used in the printed proof: a nontrivial
normal Kazhdan subgroup of a subgroup killed in every normalized-HS
ultraproduct rules out `WeakMF`. -/
theorem manuscriptNormalKazhdanMovingCornerWeakMFObstruction
    (G : Type) [Group G] [Countable G]
    (D K : Subgroup G) [K.Normal] [Nontrivial K]
    (hkill : ∀ (B : OpAlmostRepresentation G) (U : Ultrafilter ℕ)
      (hcof : (U : Filter ℕ) ≤ Filter.cofinite) (x : G), x ∈ D →
      (KazhdanCompressionCore.toAsymptoticUnitaryRepresentation B).toUltraproductHom
        hcof x = 1)
    (hT : HasKazhdanPropertyT.{0, 0} K) (hK : K ≤ D) :
    ¬ IsWeakMF G := by
  exact KazhdanCompressionCore.not_isWeakMF_of_normalKazhdan_le_hyperlinear_killed
    D hkill K hT hK

/-- The range of a homomorphism into an operator-norm matrix ultraproduct is
countable, operator-MF, and `WeakMF`. -/
theorem manuscriptNormUltraproductRangeMFPackage
    (G : Type) [Group G] [Countable G]
    (I : Type) (U : Ultrafilter I) (X : I → FiniteModel)
    (rho : G →* UniversalWeakMF U X) :
    Countable rho.range ∧ IsOperatorMF rho.range ∧ IsWeakMF rho.range := by
  letI : Countable rho.range :=
    Function.Surjective.countable rho.rangeRestrict_surjective
  have hres : normMFResidual rho.range = ⊥ := by
    apply Subgroup.eq_bot_iff_forall (normMFResidual rho.range) |>.2
    intro y hy
    apply Subtype.ext
    exact map_eq_one_of_mem_normMFResidual U X rho.range.subtype hy
  have hOperatorMF : IsOperatorMF rho.range :=
    isOperatorMF_of_normMFResidual_eq_bot hres
  have hWeakMF : IsWeakMF rho.range :=
    ⟨1, by norm_num,
      OperatorMFLocalNormalization.isNormApproximable_one hOperatorMF⟩
  exact ⟨inferInstance, hOperatorMF, hWeakMF⟩

/-- The `WeakMF` clause of the norm-ultraproduct range package. -/
theorem manuscriptNormUltraproductRangeIsWeakMF
    (G : Type) [Group G] [Countable G]
    (I : Type) (U : Ultrafilter I) (X : I → FiniteModel)
    (rho : G →* UniversalWeakMF U X) :
    IsWeakMF rho.range :=
  (manuscriptNormUltraproductRangeMFPackage G I U X rho).2.2

/-- A surviving element makes the homomorphic image of the Kazhdan subgroup
simultaneously normal, Kazhdan, and nontrivial. -/
theorem manuscriptNormalKazhdanSurvivingImage
    (G : Type) [Group G] (K : Subgroup G) [K.Normal]
    (hT : HasKazhdanPropertyT.{0, 0} K)
    (I : Type) (U : Ultrafilter I) (X : I → FiniteModel)
    (rho : G →* UniversalWeakMF U X) (k : G) (hk : k ∈ K)
    (hsurvive : rho k ≠ 1) :
    let f : G →* rho.range := rho.rangeRestrict
    let K' : Subgroup rho.range := K.map f
    K'.Normal ∧ HasKazhdanPropertyT.{0, 0} K' ∧ Nontrivial K' := by
  dsimp only
  let f : G →* rho.range := rho.rangeRestrict
  let K' : Subgroup rho.range := K.map f
  have hnormal : K'.Normal :=
    KazhdanCompressionCore.map_subgroup_normal K f
      rho.rangeRestrict_surjective
  have hT' : HasKazhdanPropertyT.{0, 0} K' :=
    KazhdanCompressionCore.map_subgroup_hasKazhdanPropertyT K f hT
  have hk' : f k ∈ K' := ⟨k, hk, rfl⟩
  have hfk_ne : f k ≠ 1 := by
    intro heq
    apply hsurvive
    exact congrArg Subtype.val heq
  have hnontrivial : Nontrivial K' :=
    ⟨⟨⟨f k, hk'⟩, 1, fun heq ↦ hfk_ne (congrArg Subtype.val heq)⟩⟩
  exact ⟨hnormal, hT', hnontrivial⟩

/-- Shadow killing passes to the range of an arbitrary homomorphism by
precomposing every target almost representation with the range restriction. -/
theorem manuscriptNormalKazhdanShadowKillPassesToRange
    (G : Type) [Group G] (D : Subgroup G)
    (hkill : ∀ (B : OpAlmostRepresentation G) (U : Ultrafilter ℕ)
      (hcof : (U : Filter ℕ) ≤ Filter.cofinite) (x : G), x ∈ D →
      (KazhdanCompressionCore.toAsymptoticUnitaryRepresentation B).toUltraproductHom
        hcof x = 1)
    (I : Type) (U : Ultrafilter I) (X : I → FiniteModel)
    (rho : G →* UniversalWeakMF U X) :
    let f : G →* rho.range := rho.rangeRestrict
    ∀ (B : OpAlmostRepresentation rho.range) (U' : Ultrafilter ℕ)
      (hcof : (U' : Filter ℕ) ≤ Filter.cofinite) (y : rho.range),
      y ∈ D.map f →
      (KazhdanCompressionCore.toAsymptoticUnitaryRepresentation B).toUltraproductHom
        hcof y = 1 := by
  dsimp only
  intro B U' hcof y hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact hkill (B.comap rho.rangeRestrict) U' hcof x hx

/-- The range construction and the moving-corner obstruction force every
operator-norm matrix-ultraproduct homomorphism to kill each element of `K`. -/
theorem manuscriptNormalKazhdanEveryNormUltraproductKills
    (G : Type) [Group G] [Countable G] (D K : Subgroup G) [K.Normal]
    (hD : D ≤ opToHSShadowResidual G)
    (hT : HasKazhdanPropertyT.{0, 0} K) (hK : K ≤ D)
    (k : G) (hk : k ∈ K)
    (I : Type) (U : Ultrafilter I) (X : I → FiniteModel)
    (rho : G →* UniversalWeakMF U X) :
    rho k = 1 := by
  exact map_eq_one_of_mem_normMFResidual U X rho
    (normalKazhdan_le_normMFResidual_of_le_opToHSShadowResidual
      K hT (hK.trans hD) hk)

/-- The elementwise range contradiction is precisely membership of the whole
normal Kazhdan subgroup in the norm-MF residual. -/
theorem manuscriptNormalKazhdanMovingCornerNormResidual
    (G : Type) [Group G] [Countable G] (D K : Subgroup G) [K.Normal]
    (hD : D ≤ opToHSShadowResidual G)
    (hT : HasKazhdanPropertyT.{0, 0} K) (hK : K ≤ D) :
    K ≤ normMFResidual G := by
  exact normalKazhdan_le_normMFResidual_of_le_opToHSShadowResidual
    K hT (hK.trans hD)

/-- The moving-corner proof in the exact radical language printed by the
manuscript. -/
theorem manuscriptNormalKazhdanMovingCornerRadical : NormalKazhdanRadical := by
  exact manuscriptNormalKazhdanRadical

end OneSidedMFRadical
end Manuscript
end GroupApproximation
