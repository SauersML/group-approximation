import GroupApproximation.Kazhdan.HaagerupAffineSums
import GroupApproximation.Kazhdan.BruhatTitsTwoTree
import GroupApproximation.Algebra.LaurentBinaryPlaces
import GroupApproximation.Meta.AxiomGuard

/-!
# `GL_2(F_2[z,z^{-1}])` has the Haagerup property

`non_mf_groups_exist.tex`, the remark after `prop:torsion-defect-ring` (tex lines 1146--1151):

> Every countable subgroup of `GL_2` over a field has the Haagerup property, and the kernel of
> `GL_2(J) → GL_2(F_2[z,z^{-1}])` is locally finite, so a Kazhdan subgroup of `GL_2(J)` has
> finite image …

This module proves the printed Haagerup property for the target of the printed argument, by the
Guentner--Higson--Weinberger method and with no literature input.  `GL_2(F_2[z,z^{-1}])` embeds in
`GL_2(F_2((z)))` through the two places `z ↦ z` and `z ↦ z^{-1}`, and acts on the sum of

* the half-space actions of the two Bruhat--Tits trees (`placeTreeAction`), whose squared
  translation parts dominate the displacements `dispInt` (`dispInt_le_norm_sq_placeTreeAction`);
* the translations of the line by the valuations of the determinant at the two places.

If all four translation parts are at most `R`, every nonzero entry has valuation at least `-N`
at both places for `N > R² + R`, and such Laurent polynomials form a finite set
(`finite_of_bounded_places`).  So the sum is proper (`hasHaagerupProperty_binaryLaurentGL`), and
with Delorme's theorem every Kazhdan subgroup is finite (`finite_of_hasKazhdanPropertyT_of_haagerup`).
-/

namespace GroupApproximation
namespace JacobsonLaurent

open ValuedMatrixTwo Haagerup

section Place

variable (ι : BinaryLaurent →+* BinaryLaurentSeries)

/-- `GL_2(F_2[z,z^{-1}])` acting on the Bruhat--Tits tree of `F_2((z))` through `ι`. -/
noncomputable def placeTreeAction : AffineAction.{0, 0} (GL (Fin 2) BinaryLaurent) := by
  letI : MulAction (GL (Fin 2) BinaryLaurent) (Vertex zVal) :=
    MulAction.compHom _ (Matrix.GeneralLinearGroup.map ι)
  exact treeAction (btGraph_isTree zVal zVal_zSeries)
    (fun g x y ↦ btGraph_isGraphAction zVal (Matrix.GeneralLinearGroup.map ι g) x y)
    (QuotientGroup.mk 1 : Vertex zVal)

/-- The displacement on the tree is at most the squared translation part. -/
theorem dispInt_le_norm_sq_placeTreeAction (g : GL (Fin 2) BinaryLaurent) :
    (dispInt zVal (Matrix.GeneralLinearGroup.map ι g) : ℝ) ≤ ‖(placeTreeAction ι).b g‖ ^ 2 := by
  letI : MulAction (GL (Fin 2) BinaryLaurent) (Vertex zVal) :=
    MulAction.compHom _ (Matrix.GeneralLinearGroup.map ι)
  have h1 := dist_le_norm_sq_treeAction (btGraph_isTree zVal zVal_zSeries)
    (fun g x y ↦ btGraph_isGraphAction zVal (Matrix.GeneralLinearGroup.map ι g) x y)
    (QuotientGroup.mk 1 : Vertex zVal) g
  have hsmul : g • (QuotientGroup.mk 1 : Vertex zVal) =
      QuotientGroup.mk (Matrix.GeneralLinearGroup.map ι g) := by
    show Matrix.GeneralLinearGroup.map ι g • (QuotientGroup.mk 1 : Vertex zVal) = _
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  have h2 := LevelTree.level_le_add_dist (level zVal) (fun _ _ h ↦ level_adj zVal h)
    (btGraph_connected zVal zVal_zSeries) (QuotientGroup.mk 1 : Vertex zVal)
    (QuotientGroup.mk (Matrix.GeneralLinearGroup.map ι g))
  rw [level_mk, level_mk, dispInt_one, Int.toNat_zero, zero_add] at h2
  have hnn := dispInt_nonneg zVal (Matrix.GeneralLinearGroup.map ι g)
  have h3 : (dispInt zVal (Matrix.GeneralLinearGroup.map ι g) : ℝ) ≤
      ((btGraph zVal).dist (QuotientGroup.mk 1) (g • (QuotientGroup.mk 1 : Vertex zVal)) : ℕ) := by
    rw [hsmul]
    have h4 : dispInt zVal (Matrix.GeneralLinearGroup.map ι g) ≤
        ((btGraph zVal).dist (QuotientGroup.mk 1)
          (QuotientGroup.mk (Matrix.GeneralLinearGroup.map ι g)) : ℤ) := by
      omega
    exact_mod_cast h4
  exact h3.trans h1

/-- The valuation of the determinant at the place `ι`, as a homomorphism to `ℤ`. -/
noncomputable def placeDetVal : GL (Fin 2) BinaryLaurent →* Multiplicative ℤ where
  toFun g := Multiplicative.ofAdd (vz zVal
    ((Matrix.GeneralLinearGroup.map ι g : GL (Fin 2) BinaryLaurentSeries) :
      Matrix (Fin 2) (Fin 2) BinaryLaurentSeries).det)
  map_one' := by
    rw [map_one, Units.val_one, Matrix.det_one, vz_one, ofAdd_zero]
  map_mul' g h := by
    rw [map_mul, vz_det_mul, ofAdd_add]

/-- Bounded translation parts at a place bound the valuations of the entries from below. -/
theorem neg_le_vz_entry_of_bounds {g : GL (Fin 2) BinaryLaurent} {R : ℝ} {N : ℕ}
    (hRN : R ^ 2 ≤ N ∧ R ≤ N) (htree : ‖(placeTreeAction ι).b g‖ ≤ R)
    (hdetb : ‖(intAction (placeDetVal ι)).b g‖ ≤ R) (i j : Fin 2)
    (hij : ι ((g : Matrix (Fin 2) (Fin 2) BinaryLaurent) i j) ≠ 0) :
    -(N : ℤ) ≤ vz zVal (ι ((g : Matrix (Fin 2) (Fin 2) BinaryLaurent) i j)) := by
  have hentry : ∀ i j : Fin 2,
      ((Matrix.GeneralLinearGroup.map ι g : GL (Fin 2) BinaryLaurentSeries) :
        Matrix (Fin 2) (Fin 2) BinaryLaurentSeries) i j =
        ι ((g : Matrix (Fin 2) (Fin 2) BinaryLaurent) i j) :=
    fun i j ↦ Matrix.GeneralLinearGroup.map_apply _ i j _
  have hd : (dispInt zVal (Matrix.GeneralLinearGroup.map ι g) : ℝ) ≤ N :=
    (dispInt_le_norm_sq_placeTreeAction ι g).trans
      ((pow_le_pow_left₀ (norm_nonneg _) htree 2).trans hRN.1)
  have hd' : dispInt zVal (Matrix.GeneralLinearGroup.map ι g) ≤ N := by exact_mod_cast hd
  have habs := (norm_intAction_b (placeDetVal ι) g).symm.trans_le hdetb
  have hdetR : -(N : ℝ) ≤ ((Multiplicative.toAdd (placeDetVal ι g) : ℤ) : ℝ) := by
    linarith [(abs_le.mp habs).1, hRN.2]
  have hdet : -(N : ℤ) ≤ vz zVal
      ((Matrix.GeneralLinearGroup.map ι g : GL (Fin 2) BinaryLaurentSeries) :
        Matrix (Fin 2) (Fin 2) BinaryLaurentSeries).det := by
    exact_mod_cast hdetR
  have hmin := entriesGe_entryMin zVal (Matrix.GeneralLinearGroup.map ι g) i j
    (by rw [hentry]; exact hij)
  rw [hentry] at hmin
  unfold dispInt at hd'
  omega

end Place

/-- **`GL_2(F_2[z,z^{-1}])` has the Haagerup property.** -/
theorem hasHaagerupProperty_binaryLaurentGL :
    HasHaagerupProperty.{0, 0} (GL (Fin 2) BinaryLaurent) := by
  classical
  refine hasHaagerupProperty_of_finite_sum
    ![placeTreeAction iotaZero, placeTreeAction iotaInf, intAction (placeDetVal iotaZero),
      intAction (placeDetVal iotaInf)] fun R ↦ ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (R ^ 2 + R)
  let F : Set BinaryLaurent :=
    {a | a ≠ 0 → -(N : ℤ) ≤ vz zVal (iotaZero a) ∧ -(N : ℤ) ≤ vz zVal (iotaInf a)}
  have hF : F.Finite := finite_of_bounded_places N
  haveI : Finite F := hF.to_subtype
  have hmem : ∀ g : GL (Fin 2) BinaryLaurent,
      (∀ k, ‖(![placeTreeAction iotaZero, placeTreeAction iotaInf,
        intAction (placeDetVal iotaZero), intAction (placeDetVal iotaInf)] k).b g‖ ≤ R) →
      ∀ i j, (g : Matrix (Fin 2) (Fin 2) BinaryLaurent) i j ∈ F := by
    intro g hg i j hne
    have h0 : ‖(placeTreeAction iotaZero).b g‖ ≤ R := hg 0
    have h1 : ‖(placeTreeAction iotaInf).b g‖ ≤ R := hg 1
    have h2 : ‖(intAction (placeDetVal iotaZero)).b g‖ ≤ R := hg 2
    have h3 : ‖(intAction (placeDetVal iotaInf)).b g‖ ≤ R := hg 3
    have hR0 : 0 ≤ R := (norm_nonneg _).trans h0
    have hRN : R ^ 2 ≤ N ∧ R ≤ N := ⟨by nlinarith [sq_nonneg R], by nlinarith [sq_nonneg R]⟩
    exact ⟨neg_le_vz_entry_of_bounds iotaZero hRN h0 h2 i j (iotaZero_ne_zero hne),
      neg_le_vz_entry_of_bounds iotaInf hRN h1 h3 i j (iotaInf_ne_zero hne)⟩
  have hfin : Finite {g : GL (Fin 2) BinaryLaurent |
      ∀ k, ‖(![placeTreeAction iotaZero, placeTreeAction iotaInf,
        intAction (placeDetVal iotaZero), intAction (placeDetVal iotaInf)] k).b g‖ ≤ R} := by
    refine Finite.of_injective (fun g ↦ fun i j ↦ (⟨_, hmem g.1 g.2 i j⟩ : F)) ?_
    intro g h hgh
    apply Subtype.ext
    refine Matrix.GeneralLinearGroup.ext fun i j ↦ ?_
    exact congrArg Subtype.val (congrFun (congrFun hgh i) j)
  exact Set.finite_coe_iff.mp hfin

/-- **Every subgroup of `GL_2(F_2[z,z^{-1}])` has the Haagerup property.** -/
theorem hasHaagerupProperty_binaryLaurentGL_subgroup (L : Subgroup (GL (Fin 2) BinaryLaurent)) :
    HasHaagerupProperty.{0, 0} L :=
  hasHaagerupProperty_binaryLaurentGL.subgroup L

/-- **The printed route.**  A Kazhdan subgroup of `GL_2(F_2[z,z^{-1}])` has property `(T)` and
the Haagerup property, so it is finite by Delorme's theorem. -/
theorem finite_of_hasKazhdanPropertyT_of_haagerup (L : Subgroup (GL (Fin 2) BinaryLaurent))
    (hL : HasKazhdanPropertyT.{0, 0} L) : Finite L :=
  finite_of_hasKazhdanPropertyT_of_hasHaagerupProperty hL
    (hasHaagerupProperty_binaryLaurentGL_subgroup L)

end JacobsonLaurent
end GroupApproximation

#audit_axioms GroupApproximation.JacobsonLaurent.hasHaagerupProperty_binaryLaurentGL
#audit_axioms GroupApproximation.JacobsonLaurent.finite_of_hasKazhdanPropertyT_of_haagerup
