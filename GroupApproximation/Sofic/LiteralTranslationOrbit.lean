import GroupApproximation.Sofic.LiteralBaseAffineQuotient
import GroupApproximation.Sofic.LiteralBaseTranslationLattice

/-!
# Two rotation conjugates suffice for every literal translation

This file isolates the elementary orbit calculation behind the relative
property-`(T)` part of the literal affine base.  Three explicit words in the
rotation generators act on the translation lattice as the elementary
transvections `E₁₃`, `E₂₃`, and `E₃₂`.  Consequently every lattice vector is
the sum of two rotation translates of standard basis vectors.

All equalities are proved inside the twenty-relator presented group.  The
matrix realization is used only to distinguish two elements already known to
belong to the translation subgroup, where it is faithful by
`latticeToBase_injective`.
-/

namespace GroupApproximation
namespace LiteralTranslationOrbit

open ExplicitLinearModel LiteralNonMFLinearWitness
open LiteralBaseAffineQuotient
open LiteralBaseRelations LiteralBaseTranslationNormal
open LiteralBaseTranslationLattice

noncomputable section

private abbrev Base := LiteralNonMFPresentation.Base

/-- The short rotation word whose lattice action is `E₁₃`. -/
def e13 : Base := x * z * y⁻¹ * x⁻¹ * y⁻¹

/-- The short rotation word whose lattice action is `E₂₃`. -/
def e23 : Base := x⁻¹ * y⁻¹ * x * z * y⁻¹

/-- The short rotation word whose lattice action is `E₃₂`. -/
def e32 : Base := x⁻¹ * z * y⁻¹ * x⁻¹ * y⁻¹ * x⁻¹

theorem e13_mem_rotations : e13 ∈ rotations := by
  exact rotations.mul_mem
    (rotations.mul_mem
      (rotations.mul_mem
        (rotations.mul_mem x_mem_rotations z_mem_rotations)
        (rotations.inv_mem y_mem_rotations))
      (rotations.inv_mem x_mem_rotations))
    (rotations.inv_mem y_mem_rotations)

theorem e23_mem_rotations : e23 ∈ rotations := by
  exact rotations.mul_mem
    (rotations.mul_mem
      (rotations.mul_mem
        (rotations.mul_mem
          (rotations.inv_mem x_mem_rotations)
          (rotations.inv_mem y_mem_rotations))
        x_mem_rotations)
      z_mem_rotations)
    (rotations.inv_mem y_mem_rotations)

theorem e32_mem_rotations : e32 ∈ rotations := by
  exact rotations.mul_mem
    (rotations.mul_mem
      (rotations.mul_mem
        (rotations.mul_mem
          (rotations.mul_mem
            (rotations.inv_mem x_mem_rotations) z_mem_rotations)
          (rotations.inv_mem y_mem_rotations))
        (rotations.inv_mem x_mem_rotations))
      (rotations.inv_mem y_mem_rotations))
    (rotations.inv_mem x_mem_rotations)

/-- The direct translation-matrix representation is faithful. -/
theorem latticeMatrixHom_injective : Function.Injective latticeMatrixHom := by
  intro a b hab
  apply Multiplicative.toAdd.injective
  funext i
  have hentry := congrArg
    (fun g : Matˣ ↦ (((g : Mat) i.castSucc 3))) hab
  change (translationMatrix a.toAdd) i.castSucc 3 =
    (translationMatrix b.toAdd) i.castSucc 3 at hentry
  fin_cases i <;> simpa [translationMatrix] using hentry

/-- Evaluation of the public matrix realization on the embedded lattice. -/
private theorem subtype_affineQuotient_latticeToBase
    (u : Multiplicative LiteralBaseTranslationLattice.Lattice) :
    gammaBar.subtype (affineQuotient (latticeToBase u)) = latticeMatrixHom u := by
  rw [lattice_eq_basis_product u]
  simp [latticeToBase_basis_zero, latticeToBase_basis_one,
    latticeToBase_basis_two, v1G, v2G, v3G]

/-- The affine matrix realization is injective after restriction to the
literal translation subgroup. -/
theorem affineQuotient_injective_on_translations {a b : Base}
    (ha : a ∈ translations) (hb : b ∈ translations)
    (hab : affineQuotient a = affineQuotient b) : a = b := by
  have ha' : a ∈ latticeToBase.range := by
    rw [latticeToBase_range]
    exact ha
  have hb' : b ∈ latticeToBase.range := by
    rw [latticeToBase_range]
    exact hb
  rcases ha' with ⟨u, rfl⟩
  rcases hb' with ⟨v, rfl⟩
  have hmatrix := congrArg gammaBar.subtype hab
  rw [subtype_affineQuotient_latticeToBase u,
    subtype_affineQuotient_latticeToBase v] at hmatrix
  exact congrArg latticeToBase (latticeMatrixHom_injective hmatrix)

private theorem e13_conj_v3_mem : e13 * v3 * e13⁻¹ ∈ translations := by
  have he : e13 ∈ Subgroup.normalizer translations := by
    rw [normalizer_translations_eq_top]
    exact Subgroup.mem_top e13
  exact ((Subgroup.mem_normalizer_iff.mp he) v3).mp v3_mem_translations

private theorem e23_conj_v3_mem : e23 * v3 * e23⁻¹ ∈ translations := by
  have he : e23 ∈ Subgroup.normalizer translations := by
    rw [normalizer_translations_eq_top]
    exact Subgroup.mem_top e23
  exact ((Subgroup.mem_normalizer_iff.mp he) v3).mp v3_mem_translations

private theorem e32_conj_v2_mem : e32 * v2 * e32⁻¹ ∈ translations := by
  have he : e32 ∈ Subgroup.normalizer translations := by
    rw [normalizer_translations_eq_top]
    exact Subgroup.mem_top e32
  exact ((Subgroup.mem_normalizer_iff.mp he) v2).mp v2_mem_translations

private theorem conjugate_mem_translations (g u : Base)
    (hu : u ∈ translations) : g * u * g⁻¹ ∈ translations := by
  have hg : g ∈ Subgroup.normalizer translations := by
    rw [normalizer_translations_eq_top]
    exact Subgroup.mem_top g
  exact ((Subgroup.mem_normalizer_iff.mp hg) u).mp hu

/-- The first short word sends the third basis translation to `v1 * v3`. -/
theorem e13_conj_v3 : e13 * v3 * e13⁻¹ = v1 * v3 := by
  apply affineQuotient_injective_on_translations e13_conj_v3_mem
    (translations.mul_mem v1_mem_translations v3_mem_translations)
  simp only [e13, map_mul, map_inv, affineQuotient_generator,
    matrixBaseGenerator_x, matrixBaseGenerator_y, matrixBaseGenerator_z,
    matrixBaseGenerator_v1, matrixBaseGenerator_v3]
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [xG, yG, zG, v1G, v3G, xU, yU, zU, v1U, v3U,
      xM, yM, zM, v1M, v3M, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The second short word sends the third basis translation to `v2 * v3`. -/
theorem e23_conj_v3 : e23 * v3 * e23⁻¹ = v2 * v3 := by
  apply affineQuotient_injective_on_translations e23_conj_v3_mem
    (translations.mul_mem v2_mem_translations v3_mem_translations)
  simp only [e23, map_mul, map_inv, affineQuotient_generator,
    matrixBaseGenerator_x, matrixBaseGenerator_y, matrixBaseGenerator_z,
    matrixBaseGenerator_v2, matrixBaseGenerator_v3]
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [xG, yG, zG, v2G, v3G, xU, yU, zU, v2U, v3U,
      xM, yM, zM, v2M, v3M, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The third short word sends the second basis translation to `v2 * v3`. -/
theorem e32_conj_v2 : e32 * v2 * e32⁻¹ = v2 * v3 := by
  apply affineQuotient_injective_on_translations e32_conj_v2_mem
    (translations.mul_mem v2_mem_translations v3_mem_translations)
  simp only [e32, map_mul, map_inv, affineQuotient_generator,
    matrixBaseGenerator_x, matrixBaseGenerator_y, matrixBaseGenerator_z,
    matrixBaseGenerator_v2, matrixBaseGenerator_v3]
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [xG, yG, zG, v2G, v3G, xU, yU, zU, v2U, v3U,
      xM, yM, zM, v2M, v3M, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The `E₁₃` word fixes the first basis translation. -/
theorem e13_conj_v1 : e13 * v1 * e13⁻¹ = v1 := by
  apply affineQuotient_injective_on_translations
    (conjugate_mem_translations e13 v1 v1_mem_translations)
    v1_mem_translations
  simp only [e13, map_mul, map_inv, affineQuotient_generator,
    matrixBaseGenerator_x, matrixBaseGenerator_y, matrixBaseGenerator_z,
    matrixBaseGenerator_v1]
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [xG, yG, zG, v1G, xU, yU, zU, v1U,
      xM, yM, zM, v1M, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The `E₁₃` word fixes the second basis translation. -/
theorem e13_conj_v2 : e13 * v2 * e13⁻¹ = v2 := by
  apply affineQuotient_injective_on_translations
    (conjugate_mem_translations e13 v2 v2_mem_translations)
    v2_mem_translations
  simp only [e13, map_mul, map_inv, affineQuotient_generator,
    matrixBaseGenerator_x, matrixBaseGenerator_y, matrixBaseGenerator_z,
    matrixBaseGenerator_v2]
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [xG, yG, zG, v2G, xU, yU, zU, v2U,
      xM, yM, zM, v2M, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The `E₂₃` word fixes the second basis translation. -/
theorem e23_conj_v2 : e23 * v2 * e23⁻¹ = v2 := by
  apply affineQuotient_injective_on_translations
    (conjugate_mem_translations e23 v2 v2_mem_translations)
    v2_mem_translations
  simp only [e23, map_mul, map_inv, affineQuotient_generator,
    matrixBaseGenerator_x, matrixBaseGenerator_y, matrixBaseGenerator_z,
    matrixBaseGenerator_v2]
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [xG, yG, zG, v2G, xU, yU, zU, v2U,
      xM, yM, zM, v2M, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The `E₃₂` word fixes the third basis translation. -/
theorem e32_conj_v3 : e32 * v3 * e32⁻¹ = v3 := by
  apply affineQuotient_injective_on_translations
    (conjugate_mem_translations e32 v3 v3_mem_translations)
    v3_mem_translations
  simp only [e32, map_mul, map_inv, affineQuotient_generator,
    matrixBaseGenerator_x, matrixBaseGenerator_y, matrixBaseGenerator_z,
    matrixBaseGenerator_v3]
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [xG, yG, zG, v3G, xU, yU, zU, v3U,
      xM, yM, zM, v3M, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Iterating a transvection conjugation adds the corresponding integral
multiple of the fixed direction. -/
private theorem zpow_conj_of_transvection {G : Type*} [Group G]
    {e u v : G} (heu : Commute e u) (_huv : Commute u v)
    (hstep : e * v * e⁻¹ = u * v) (n : ℤ) :
    e ^ n * v * (e ^ n)⁻¹ = u ^ n * v := by
  have hstep' : e * v = u * v * e := by rw [← hstep]; group
  have hback' : e⁻¹ * v = u⁻¹ * v * e⁻¹ := by
    have h1 : v * e⁻¹ = e⁻¹ * (u * v) := by rw [← hstep]; group
    have h2 : e⁻¹ * (u * v) = u * (e⁻¹ * v) := by
      rw [← mul_assoc, heu.inv_left.eq, mul_assoc]
    calc
      e⁻¹ * v = u⁻¹ * (u * (e⁻¹ * v)) := by group
      _ = u⁻¹ * (e⁻¹ * (u * v)) := by rw [h2]
      _ = u⁻¹ * (v * e⁻¹) := by rw [h1]
      _ = u⁻¹ * v * e⁻¹ := by group
  have key : e ^ n * v = u ^ n * v * e ^ n := by
    induction n using Int.induction_on with
    | zero => simp
    | succ m ih =>
        calc
          e ^ ((m : ℤ) + 1) * v = e ^ (m : ℤ) * (e * v) := by
            rw [zpow_add_one]; group
          _ = e ^ (m : ℤ) * (u * v * e) := by rw [hstep']
          _ = e ^ (m : ℤ) * u * v * e := by group
          _ = u * e ^ (m : ℤ) * v * e := by
            rw [(heu.zpow_left (m : ℤ)).eq]
          _ = u * (e ^ (m : ℤ) * v) * e := by group
          _ = u * (u ^ (m : ℤ) * v * e ^ (m : ℤ)) * e := by rw [ih]
          _ = u ^ ((m : ℤ) + 1) * v * e ^ ((m : ℤ) + 1) := by
            rw [zpow_add_one, zpow_add_one]; group
    | pred m ih =>
        calc
          e ^ (-(m : ℤ) - 1) * v = e ^ (-(m : ℤ)) * (e⁻¹ * v) := by
            rw [zpow_sub_one]; group
          _ = e ^ (-(m : ℤ)) * (u⁻¹ * v * e⁻¹) := by rw [hback']
          _ = e ^ (-(m : ℤ)) * u⁻¹ * v * e⁻¹ := by group
          _ = u⁻¹ * e ^ (-(m : ℤ)) * v * e⁻¹ := by
            rw [((heu.zpow_left (-(m : ℤ))).inv_right).eq]
          _ = u⁻¹ * (e ^ (-(m : ℤ)) * v) * e⁻¹ := by group
          _ = u⁻¹ * (u ^ (-(m : ℤ)) * v * e ^ (-(m : ℤ))) * e⁻¹ := by
            rw [ih]
          _ = u ^ (-(m : ℤ) - 1) * v * e ^ (-(m : ℤ) - 1) := by
            rw [zpow_sub_one, zpow_sub_one]; group
  calc
    e ^ n * v * (e ^ n)⁻¹ = (u ^ n * v * e ^ n) * (e ^ n)⁻¹ := by rw [key]
    _ = u ^ n * v := by group

private theorem commute_of_conj_eq_self {G : Type*} [Group G] {g u : G}
    (h : g * u * g⁻¹ = u) : Commute g u := by
  rw [Commute]
  calc
    g * u = (g * u * g⁻¹) * g := by group
    _ = u * g := by rw [h]

private theorem e13_zpow_conj_v3 (n : ℤ) :
    e13 ^ n * v3 * (e13 ^ n)⁻¹ = v1 ^ n * v3 :=
  zpow_conj_of_transvection
    (commute_of_conj_eq_self e13_conj_v1)
    (translations_commute v1_mem_translations v3_mem_translations)
    e13_conj_v3 n

private theorem e13_zpow_conj_v2 (n : ℤ) :
    e13 ^ n * v2 * (e13 ^ n)⁻¹ = v2 := by
  have hcomm := commute_of_conj_eq_self e13_conj_v2
  rw [(hcomm.zpow_left n).eq]
  group

private theorem e23_zpow_conj_v3 (n : ℤ) :
    e23 ^ n * v3 * (e23 ^ n)⁻¹ = v2 ^ n * v3 :=
  zpow_conj_of_transvection
    (commute_of_conj_eq_self e23_conj_v2)
    (translations_commute v2_mem_translations v3_mem_translations)
    e23_conj_v3 n

private theorem e32_zpow_conj_v2 (n : ℤ) :
    e32 ^ n * v2 * (e32 ^ n)⁻¹ = v2 * v3 ^ n := by
  have h := zpow_conj_of_transvection
    (commute_of_conj_eq_self e32_conj_v3)
    (translations_commute v3_mem_translations v2_mem_translations)
    (by
      rw [← (translations_commute v2_mem_translations
        v3_mem_translations).eq]
      exact e32_conj_v2) n
  calc
    e32 ^ n * v2 * (e32 ^ n)⁻¹ = v3 ^ n * v2 := h
    _ = v2 * v3 ^ n :=
      (translations_commute v3_mem_translations v2_mem_translations).zpow_left n |>.eq

/-- Every integral translation is a product of two conjugates of the fixed
basis translations `v3` and `v2` by elements of the rotation subgroup.

This is the elementary relative-`(T)` orbit calculation for the literal
affine base; notably, the number of conjugates is uniformly two, independent
of the lattice coordinates. -/
theorem latticeTranslation_eq_two_rotation_conjugates
    (a : Multiplicative Lattice) :
    ∃ r s : rotations,
      latticeToBase a =
        (r : Base) * v3 * (r : Base)⁻¹ *
          ((s : Base) * v2 * (s : Base)⁻¹) := by
  let m : ℤ := a.toAdd 0
  let n : ℤ := a.toAdd 1 - 1
  let k : ℤ := a.toAdd 2 - 1
  let r : rotations :=
    ⟨e13 ^ m * e23 ^ n,
      rotations.mul_mem (rotations.zpow_mem e13_mem_rotations m)
        (rotations.zpow_mem e23_mem_rotations n)⟩
  let s : rotations :=
    ⟨e32 ^ k, rotations.zpow_mem e32_mem_rotations k⟩
  refine ⟨r, s, ?_⟩
  have hr : (r : Base) * v3 * (r : Base)⁻¹ =
      v1 ^ m * v2 ^ n * v3 := by
    dsimp only [r]
    calc
      (e13 ^ m * e23 ^ n) * v3 * (e13 ^ m * e23 ^ n)⁻¹ =
          e13 ^ m * (e23 ^ n * v3 * (e23 ^ n)⁻¹) *
            (e13 ^ m)⁻¹ := by group
      _ = e13 ^ m * (v2 ^ n * v3) * (e13 ^ m)⁻¹ := by
        rw [e23_zpow_conj_v3]
      _ = (e13 ^ m * v2 ^ n * (e13 ^ m)⁻¹) *
            (e13 ^ m * v3 * (e13 ^ m)⁻¹) := by group
      _ = v2 ^ n * (v1 ^ m * v3) := by
        have hc :=
          ((commute_of_conj_eq_self e13_conj_v2).zpow_zpow m n).eq
        rw [hc, e13_zpow_conj_v3]
        group
      _ = v1 ^ m * v2 ^ n * v3 := by
        have hcomm := translations_commute v1_mem_translations
          v2_mem_translations
        rw [← mul_assoc, ← (hcomm.zpow_zpow m n).eq]
  have hs : (s : Base) * v2 * (s : Base)⁻¹ = v2 * v3 ^ k := by
    simpa only [s] using e32_zpow_conj_v2 k
  rw [lattice_eq_basis_product a, map_mul, map_mul, map_zpow, map_zpow,
    map_zpow, latticeToBase_basis_zero, latticeToBase_basis_one,
    latticeToBase_basis_two, hr, hs]
  dsimp only [m, n, k]
  have h23 := translations_commute v2_mem_translations v3_mem_translations
  calc
    v1 ^ a.toAdd 0 * v2 ^ a.toAdd 1 * v3 ^ a.toAdd 2 =
        v1 ^ a.toAdd 0 * (v2 ^ (a.toAdd 1 - 1) * v2) *
          (v3 * v3 ^ (a.toAdd 2 - 1)) := by
      rw [← zpow_add_one, sub_add_cancel]
      rw [show v3 * v3 ^ (a.toAdd 2 - 1) =
          v3 ^ (a.toAdd 2 - 1) * v3 from
        (Commute.self_zpow v3 (a.toAdd 2 - 1)).eq]
      rw [← zpow_add_one, sub_add_cancel]
    _ = (v1 ^ a.toAdd 0 * v2 ^ (a.toAdd 1 - 1) * v3) *
        (v2 * v3 ^ (a.toAdd 2 - 1)) := by
      calc
        v1 ^ a.toAdd 0 * (v2 ^ (a.toAdd 1 - 1) * v2) *
            (v3 * v3 ^ (a.toAdd 2 - 1)) =
            v1 ^ a.toAdd 0 * v2 ^ (a.toAdd 1 - 1) * (v2 * v3) *
              v3 ^ (a.toAdd 2 - 1) := by group
        _ = v1 ^ a.toAdd 0 * v2 ^ (a.toAdd 1 - 1) * (v3 * v2) *
              v3 ^ (a.toAdd 2 - 1) := by rw [h23.eq]
        _ = (v1 ^ a.toAdd 0 * v2 ^ (a.toAdd 1 - 1) * v3) *
              (v2 * v3 ^ (a.toAdd 2 - 1)) := by group

/-- Subgroup-facing form of
`latticeTranslation_eq_two_rotation_conjugates`. -/
theorem translation_eq_two_rotation_conjugates {t : Base}
    (ht : t ∈ translations) :
    ∃ r s : rotations,
      t = (r : Base) * v3 * (r : Base)⁻¹ *
        ((s : Base) * v2 * (s : Base)⁻¹) := by
  have ht' : t ∈ latticeToBase.range := by
    rw [latticeToBase_range]
    exact ht
  obtain ⟨a, rfl⟩ := ht'
  exact latticeTranslation_eq_two_rotation_conjugates a

section Displacement

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem norm_mul_displacement_le
    (rho : Base →* (E ≃ₗᵢ[ℝ] E)) (a b : Base) (p : E) :
    ‖rho (a * b) p - p‖ ≤ ‖rho a p - p‖ + ‖rho b p - p‖ := by
  calc
    ‖rho (a * b) p - p‖ =
        ‖rho a (rho b p - p) + (rho a p - p)‖ := by
      congr 1
      simp only [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply,
        map_sub]
      abel
    _ ≤ ‖rho a (rho b p - p)‖ + ‖rho a p - p‖ := norm_add_le _ _
    _ = ‖rho b p - p‖ + ‖rho a p - p‖ := by rw [(rho a).norm_map]
    _ = ‖rho a p - p‖ + ‖rho b p - p‖ := add_comm _ _

private theorem norm_conjugate_displacement_eq
    (rho : Base →* (E ≃ₗᵢ[ℝ] E)) (p : E)
    (hfixed : ∀ r : rotations, rho (r : Base) p = p)
    (r : rotations) (v : Base) :
    ‖rho ((r : Base) * v * (r : Base)⁻¹) p - p‖ = ‖rho v p - p‖ := by
  have hr : rho (r : Base) p = p := hfixed r
  have hri : (rho (r : Base))⁻¹ p = p := by
    have h := congrArg (fun q : E ↦ (rho (r : Base))⁻¹ q) hr
    simpa using h.symm
  calc
    ‖rho ((r : Base) * v * (r : Base)⁻¹) p - p‖ =
        ‖rho (r : Base) (rho v p - p)‖ := by
      congr 1
      simp only [map_mul, map_inv, LinearIsometryEquiv.coe_mul,
        Function.comp_apply, map_sub, hri, hr]
    _ = ‖rho v p - p‖ := (rho (r : Base)).norm_map _

/-- A vector fixed by all literal rotations has uniformly bounded
translation orbit: every translation moves it by at most the sum of the
displacements of `v3` and `v2`.

This is the quantitative relative-`(T)` consequence of the two-conjugate
normal form and is independent of the lattice coordinates. -/
theorem norm_translation_displacement_le_of_rotations_fixed
    (rho : Base →* (E ≃ₗᵢ[ℝ] E)) (p : E)
    (hfixed : ∀ r : rotations, rho (r : Base) p = p)
    {t : Base} (ht : t ∈ translations) :
    ‖rho t p - p‖ ≤ ‖rho v3 p - p‖ + ‖rho v2 p - p‖ := by
  obtain ⟨r, s, hrs⟩ := translation_eq_two_rotation_conjugates ht
  rw [hrs]
  calc
    ‖rho (((r : Base) * v3 * (r : Base)⁻¹) *
        ((s : Base) * v2 * (s : Base)⁻¹)) p - p‖ ≤
        ‖rho ((r : Base) * v3 * (r : Base)⁻¹) p - p‖ +
          ‖rho ((s : Base) * v2 * (s : Base)⁻¹) p - p‖ :=
      norm_mul_displacement_le rho _ _ p
    _ = ‖rho v3 p - p‖ + ‖rho v2 p - p‖ := by
      rw [norm_conjugate_displacement_eq rho p hfixed r v3,
        norm_conjugate_displacement_eq rho p hfixed s v2]

end Displacement

end

end LiteralTranslationOrbit
end GroupApproximation
