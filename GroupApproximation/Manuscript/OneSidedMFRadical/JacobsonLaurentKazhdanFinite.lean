import GroupApproximation.Algebra.LaurentBinaryPlaces
import GroupApproximation.Kazhdan.BruhatTitsTwoTree
import GroupApproximation.Kazhdan.AmenableKazhdanFinite
import GroupApproximation.Sofic.SoficByAmenablePermanence
import GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonRankTwoInert
import GroupApproximation.Algebra.LaurentBinaryHaagerup

/-!
# Kazhdan subgroups of `GL_2(F_2[z, z^{-1}])` are finite

`non_mf_groups_exist.tex`, the remark after `prop:torsion-defect-ring`
(tex lines 1146--1151):

> Every countable subgroup of `GL_2` over a field has the Haagerup property, and the
> kernel of `GL_2(J) → GL_2(F_2[z,z^{-1}])` is locally finite, so a Kazhdan subgroup
> of `GL_2(J)` has finite image in `GL_2(F_2(z))` and a locally finite subgroup of
> finite index, and is finite.

The printed argument consumes the Guentner--Higson--Weinberger theorem only through
the finiteness of Kazhdan subgroups of the target.  This module proves that
finiteness for the target `GL_2(F_2[z,z^{-1}])` with no literature input:

* property `(T)` kills every homomorphism to `ℤ` (the image is a Kazhdan subgroup of
  the amenable group `ℤ`, hence finite, hence trivial), so the determinant has
  valuation zero at both places;
* at each place the group acts on the Bruhat--Tits tree
  (`ValuedMatrixTwo.exists_dispInt_bound_of_hasKazhdanPropertyT`), so the least entry
  valuation is bounded below;
* Laurent polynomials with bounded valuation at both places form a finite set
  (`JacobsonLaurent.finite_of_bounded_places`), so the group is finite.

With it, the printed deduction holds for every homomorphism with locally finite kernel
into `GL_2(F_2[z,z^{-1}])` (`manuscriptSentence_kazhdanSubgroupFiniteLaurent`).
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace JacobsonLaurentKazhdan

open JacobsonLaurent ValuedMatrixTwo

/-- **A group with property `(T)` has no nontrivial homomorphism to `ℤ`.** -/
theorem monoidHom_int_apply_eq_one {Γ : Type} [Group Γ] (hT : HasKazhdanPropertyT.{0, 0} Γ)
    (φ : Γ →* Multiplicative ℤ) (γ : Γ) : φ γ = 1 := by
  have hTM : HasKazhdanPropertyT.{0, 0} φ.range :=
    HasKazhdanPropertyT.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective hT
  haveI : Finite φ.range :=
    finite_of_isAmenable_of_kazhdan hTM (SoficByAmenablePermanence.isAmenable_int.subgroup _)
  have hpow : (φ γ) ^ Nat.card φ.range = 1 := by
    have h := congrArg Subtype.val (pow_card_eq_one' (x := (⟨φ γ, ⟨γ, rfl⟩⟩ : φ.range)))
    simpa using h
  have hn : 0 < Nat.card φ.range := Nat.card_pos
  have h := congrArg Multiplicative.toAdd hpow
  rw [toAdd_pow, toAdd_one, nsmul_eq_mul] at h
  have h0 : Multiplicative.toAdd (φ γ) = 0 :=
    (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hn.ne')
  exact Multiplicative.toAdd.injective (h0.trans toAdd_one.symm)

/-- The valuation of the determinant, as a homomorphism to `ℤ`. -/
noncomputable def detVal {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin 2) BinaryLaurentSeries) :
    Γ →* Multiplicative ℤ where
  toFun γ := Multiplicative.ofAdd
    (vz zVal ((ρ γ : GL (Fin 2) BinaryLaurentSeries) : Matrix (Fin 2) (Fin 2) BinaryLaurentSeries).det)
  map_one' := by
    rw [map_one, Units.val_one, Matrix.det_one, vz_one, ofAdd_zero]
  map_mul' g h := by
    rw [map_mul, vz_det_mul, ofAdd_add]

theorem vz_det_eq_zero {Γ : Type} [Group Γ] (hT : HasKazhdanPropertyT.{0, 0} Γ)
    (ρ : Γ →* GL (Fin 2) BinaryLaurentSeries) (γ : Γ) :
    vz zVal ((ρ γ : GL (Fin 2) BinaryLaurentSeries) : Matrix (Fin 2) (Fin 2) BinaryLaurentSeries).det
      = 0 := by
  have h := monoidHom_int_apply_eq_one hT (detVal ρ) γ
  exact Multiplicative.ofAdd.injective (h.trans ofAdd_zero.symm)

/-- At a place with determinant of valuation zero and displacement at most `N`,
every nonzero entry has valuation at least `-N`. -/
theorem neg_le_vz_entry {Γ : Type} [Group Γ] {ρ : Γ →* GL (Fin 2) BinaryLaurentSeries} {γ : Γ}
    {N : ℤ} (hdet : vz zVal ((ρ γ : GL (Fin 2) BinaryLaurentSeries) :
      Matrix (Fin 2) (Fin 2) BinaryLaurentSeries).det = 0)
    (hdisp : dispInt zVal (ρ γ) ≤ N) {i j : Fin 2}
    (hij : ((ρ γ : GL (Fin 2) BinaryLaurentSeries) : Matrix (Fin 2) (Fin 2) BinaryLaurentSeries) i j ≠ 0) :
    -N ≤ vz zVal (((ρ γ : GL (Fin 2) BinaryLaurentSeries) :
      Matrix (Fin 2) (Fin 2) BinaryLaurentSeries) i j) := by
  have hentry := entriesGe_entryMin zVal (ρ γ) i j hij
  have hnn := dispInt_nonneg zVal (ρ γ)
  unfold dispInt at hdisp hnn
  rw [hdet] at hdisp hnn
  omega

/-- **Every Kazhdan subgroup of `GL_2(F_2[z,z^{-1}])` is finite.** -/
theorem finite_of_hasKazhdanPropertyT (L : Subgroup (GL (Fin 2) BinaryLaurent))
    (hL : HasKazhdanPropertyT.{0, 0} L) : Finite L := by
  classical
  let ρ₀ : L →* GL (Fin 2) BinaryLaurentSeries :=
    (Matrix.GeneralLinearGroup.map iotaZero).comp L.subtype
  let ρ₁ : L →* GL (Fin 2) BinaryLaurentSeries :=
    (Matrix.GeneralLinearGroup.map iotaInf).comp L.subtype
  obtain ⟨R₀, hR₀⟩ := exists_dispInt_bound_of_hasKazhdanPropertyT zVal zVal_zSeries hL ρ₀
  obtain ⟨R₁, hR₁⟩ := exists_dispInt_bound_of_hasKazhdanPropertyT zVal zVal_zSeries hL ρ₁
  obtain ⟨N, hN⟩ := exists_int_ge (max R₀ R₁)
  have hdisp₀ : ∀ γ : L, dispInt zVal (ρ₀ γ) ≤ N := fun γ ↦ by
    have := (hR₀ γ).trans ((le_max_left R₀ R₁).trans hN)
    exact_mod_cast this
  have hdisp₁ : ∀ γ : L, dispInt zVal (ρ₁ γ) ≤ N := fun γ ↦ by
    have := (hR₁ γ).trans ((le_max_right R₀ R₁).trans hN)
    exact_mod_cast this
  have hval₀ : ∀ (γ : L) (i j : Fin 2),
      ((ρ₀ γ : GL (Fin 2) BinaryLaurentSeries) : Matrix (Fin 2) (Fin 2) BinaryLaurentSeries) i j =
        iotaZero (((γ : GL (Fin 2) BinaryLaurent) : Matrix (Fin 2) (Fin 2) BinaryLaurent) i j) :=
    fun γ i j ↦ Matrix.GeneralLinearGroup.map_apply _ i j _
  have hval₁ : ∀ (γ : L) (i j : Fin 2),
      ((ρ₁ γ : GL (Fin 2) BinaryLaurentSeries) : Matrix (Fin 2) (Fin 2) BinaryLaurentSeries) i j =
        iotaInf (((γ : GL (Fin 2) BinaryLaurent) : Matrix (Fin 2) (Fin 2) BinaryLaurent) i j) :=
    fun γ i j ↦ Matrix.GeneralLinearGroup.map_apply _ i j _
  let F : Set BinaryLaurent := {a | a ≠ 0 → -N ≤ vz zVal (iotaZero a) ∧ -N ≤ vz zVal (iotaInf a)}
  have hF : F.Finite := finite_of_bounded_places N
  haveI : Finite F := hF.to_subtype
  have hmem : ∀ (γ : L) (i j : Fin 2),
      (((γ : GL (Fin 2) BinaryLaurent) : Matrix (Fin 2) (Fin 2) BinaryLaurent) i j) ∈ F := by
    intro γ i j hne
    refine ⟨?_, ?_⟩
    · have h := neg_le_vz_entry (vz_det_eq_zero hL ρ₀ γ) (hdisp₀ γ) (i := i) (j := j)
        (by rw [hval₀]; exact iotaZero_ne_zero hne)
      rwa [hval₀] at h
    · have h := neg_le_vz_entry (vz_det_eq_zero hL ρ₁ γ) (hdisp₁ γ) (i := i) (j := j)
        (by rw [hval₁]; exact iotaInf_ne_zero hne)
      rwa [hval₁] at h
  refine Finite.of_injective (fun γ : L ↦ fun i j : Fin 2 ↦ (⟨_, hmem γ i j⟩ : F)) ?_
  intro γ δ hγδ
  apply Subtype.ext
  refine Matrix.GeneralLinearGroup.ext fun i j ↦ ?_
  exact congrArg Subtype.val (congrFun (congrFun hγδ i) j)

/-- **Printed (tex 1146--1151), for the printed target.**  For every homomorphism from
a group into `GL_2(F_2[z,z^{-1}])` with locally finite kernel, every Kazhdan subgroup
of the source has finite image, a locally finite subgroup of finite index, and is
finite.  The image is finite along the printed route: it has the Haagerup property
(`JacobsonLaurent.hasHaagerupProperty_binaryLaurentGL`, proved rather than cited) and
property `(T)`, so Delorme's theorem makes it finite. -/
theorem manuscriptSentence_kazhdanSubgroupFiniteLaurent :
    ∀ (G : Type) [Group G] (φ : G →* GL (Fin 2) BinaryLaurent), IsLocallyFiniteGroup φ.ker →
      ∀ L : Subgroup G, HasKazhdanPropertyT.{0, 0} L →
        Finite (L.map φ) ∧ (φ.subgroupMap L).ker.FiniteIndex ∧
          IsLocallyFiniteGroup (φ.subgroupMap L).ker ∧ Finite L := by
  intro G _ φ hker L hL
  have hTM : HasKazhdanPropertyT.{0, 0} (L.map φ) :=
    HasKazhdanPropertyT.of_surjective (φ.subgroupMap L) (φ.subgroupMap_surjective L) hL
  haveI hfinM : Finite (L.map φ) :=
    JacobsonLaurent.finite_of_hasKazhdanPropertyT_of_haagerup (L.map φ) hTM
  haveI : Finite (φ.subgroupMap L).range :=
    Finite.of_injective (fun x : (φ.subgroupMap L).range ↦ (x : L.map φ)) Subtype.val_injective
  haveI hfi : (φ.subgroupMap L).ker.FiniteIndex := inferInstance
  have hlf : IsLocallyFiniteGroup (φ.subgroupMap L).ker :=
    hker.comap (JacobsonRankTwo.kerSubgroupMapToKer φ L) (JacobsonRankTwo.kerSubgroupMapToKer_injective φ L)
  exact ⟨hfinM, hfi, hlf,
    JacobsonRankTwo.finite_of_hasKazhdanPropertyT_of_finiteIndex_locallyFinite hL _ hlf⟩

end JacobsonLaurentKazhdan
end OneSidedMFRadical
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonLaurentKazhdan.finite_of_hasKazhdanPropertyT
#audit_axioms GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonLaurentKazhdan.manuscriptSentence_kazhdanSubgroupFiniteLaurent
