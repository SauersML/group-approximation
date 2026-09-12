import GroupApproximation.Manuscript.OneSidedMFRadical.MaxInfiniteConverseRemark
import GroupApproximation.Algebra.DyadicRationals
import GroupApproximation.Meta.AxiomGuard

/-!
# The printed matrix realization of the ascending HNN base `V`

`non_mf_groups_exist.tex`, the remark after `prop:max-infinite` (tex lines
754-772):

> A group can satisfy the hypothesis of Proposition~`prop:max-infinite` and be
> MF.  The ascending HNN extension `V` of `ℤ³ ⋊ SL₃(ℤ)` along `(v,A) ↦ (2v,A)`,
> used in Section~`sec:amenable-nonqd`, has the faithful matrix realization
> `V ≅ { [[2ᵏ A, v], [0, 1]] : A ∈ SL₃(ℤ), v ∈ ℤ[1/2]³, k ∈ ℤ }`,
> and reduction modulo odd integers separates its elements, so `V` is
> residually finite and MF.  So the lamps of Section~`sec:amenable-nonqd` are
> necessary for the non-MF conclusion there.

`MaxInfiniteConverseRemark` proves the second half of that sentence — `V` is
residually finite, `V` is MF, and `V` satisfies the hypothesis of
`prop:max-infinite` — by a congruence route that never leaves `ℤ`, and records
that the displayed matrix realization is deliberately not formalized there.
This module supplies exactly that missing clause, at the printed generality.

## What is proved

`V` is the same object as in `MaxInfiniteConverseRemark`, namely
`MarkedCompression.Vertical conjD conjD_injective`: the mapping telescope of
the doubling self-embedding `α = conjD` of `Γ̄ = ℤ³ ⋊ SL₃(ℤ)`, extended by the
shift, i.e. the ascending HNN extension `⟨Γ̄, t ∣ tγt⁻¹ = α(γ)⟩`.

* `realization : V →* GL₄(ℚ)` is the universal-property extension of the
  inclusion `Γ̄ ≤ GL₄(ℚ)` by `t ↦ D = diag(2,2,2,1)`.  Conjugation by `D` is
  what `conjD` is, so the extension exists; nothing is assumed.
* `realization_injective`: the realization is *faithful*.  The telescope part
  is caught by cancellation, and the stable-letter exponent by integrality: if
  `D⁻ᵏ` lies in `Γ̄` then `2⁻ᵏ` and `2ᵏ` are both integers, so `k = 0`.
* `range_realization`: the image is *exactly* the printed set
  `{ [[2ᵏ A, v], [0,1]] : A ∈ SL₃(ℤ), v ∈ ℤ[1/2]³, k ∈ ℤ }`, spelled entry by
  entry in `printedMat`, with `ℤ[1/2] = DyadicRationals.dyadicSubring` (that
  subring is identified with `Subring.closure {1/2}` by
  `dyadicSubring_eq_closure`, which is what licenses the name).

Both inclusions of the image use completeness of the affine base, which the
repository already has: `LiteralBaseCompleteness.affineQuotient_surjective`
together with the rotation/translation splitting gives the affine normal form
`u = [[A, w],[0,1]]` of every element of `Γ̄`, and
`SL3ElementaryGeneration.toSL3_surjective` gives every `A ∈ SL₃(ℤ)` back.
Conjugating by `Dⁿ` divides the translation part by `2ⁿ`, which is where the
dyadic denominators come from; multiplying by `Dᵏ` is where `2ᵏ` does.
-/

namespace GroupApproximation
namespace AffineHNNBase

open Matrix ExplicitLinearModel MarkedCompression MappingTelescope
open SemidirectProduct LiteralBaseCompleteness LiteralP13MatrixModel
open DyadicRationals

noncomputable section

/-! ## The powers of the doubling matrix `D = diag(2,2,2,1)` -/

/-- The diagonal of `Dᵏ`. -/
def dScale (k : ℤ) : Fin 4 → ℚ := ![(2 : ℚ) ^ k, (2 : ℚ) ^ k, (2 : ℚ) ^ k, 1]

theorem dScale_zero : dScale 0 = fun _ => (1 : ℚ) := by
  funext i
  fin_cases i <;> simp [dScale]

set_option linter.unusedSimpArgs false in
theorem dM_eq_dScale : dM = Matrix.diagonal (dScale 1) := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    norm_num [dM, dScale, Matrix.diagonal_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]

set_option linter.unusedSimpArgs false in
theorem dInvM_eq_dScale : dInvM = Matrix.diagonal (dScale (-1)) := by
  have h2 : (2 : ℚ) ^ (-1 : ℤ) = 1 / 2 := by
    rw [_root_.zpow_neg, zpow_one]
    norm_num
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    norm_num [dInvM, dScale, h2, Matrix.diagonal_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]

/-- **`Dᵏ = diag(2ᵏ, 2ᵏ, 2ᵏ, 1)`** for every integer exponent. -/
theorem dU_zpow_val (k : ℤ) :
    ((dU ^ k : Matˣ) : Mat) = Matrix.diagonal (dScale k) := by
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  induction k using Int.induction_on with
  | zero =>
      rw [zpow_zero, dScale_zero, Matrix.diagonal_one]
      rfl
  | succ n ih =>
      rw [_root_.zpow_add_one, Units.val_mul, ih,
        show ((dU : Matˣ) : Mat) = dM from rfl, dM_eq_dScale,
        Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      fin_cases i <;>
        simp [dScale, zpow_add_one₀ h2]
  | pred n ih =>
      rw [_root_.zpow_sub_one, Units.val_mul, ih,
        show ((dU⁻¹ : Matˣ) : Mat) = dInvM from rfl, dInvM_eq_dScale,
        Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      fin_cases i <;>
        simp [dScale, zpow_sub_one₀ h2, _root_.zpow_neg]

theorem two_zpow_ne_zero (m : ℤ) : ((2 : ℚ) ^ m) ≠ 0 :=
  (zpow_pos (by norm_num : (0 : ℚ) < 2) m).ne'

/-! ## The affine units and the printed display -/

/-- The affine matrix unit `[[A, q], [0, 1]]`. -/
def affUnit (A : SL3) (q : Fin 3 → ℚ) : Matˣ :=
  transUnit (q 0) (q 1) (q 2) * blockEmbed4 A

theorem affUnit_vec (A : SL3) (a b c : ℚ) :
    affUnit A ![a, b, c] = transUnit a b c * blockEmbed4 A := by
  simp [affUnit]

theorem vprod_eq_transUnit (a b c : ℤ) :
    (v1U ^ a * v2U ^ b * v3U ^ c : Matˣ) = transUnit (a : ℚ) (b : ℚ) (c : ℚ) :=
  Units.ext (vprod_val a b c)

set_option linter.unusedSimpArgs false in
/-- The entries of `[[A, q], [0, 1]]`. -/
theorem affUnit_val (A : SL3) (q : Fin 3 → ℚ) :
    ((affUnit A q : Matˣ) : Mat) =
      !![((A : Matrix (Fin 3) (Fin 3) ℤ) 0 0 : ℚ),
          ((A : Matrix (Fin 3) (Fin 3) ℤ) 0 1 : ℚ),
          ((A : Matrix (Fin 3) (Fin 3) ℤ) 0 2 : ℚ), q 0;
        ((A : Matrix (Fin 3) (Fin 3) ℤ) 1 0 : ℚ),
          ((A : Matrix (Fin 3) (Fin 3) ℤ) 1 1 : ℚ),
          ((A : Matrix (Fin 3) (Fin 3) ℤ) 1 2 : ℚ), q 1;
        ((A : Matrix (Fin 3) (Fin 3) ℤ) 2 0 : ℚ),
          ((A : Matrix (Fin 3) (Fin 3) ℤ) 2 1 : ℚ),
          ((A : Matrix (Fin 3) (Fin 3) ℤ) 2 2 : ℚ), q 2;
        0, 0, 0, 1] := by
  rw [affUnit, Units.val_mul, blockEmbed4_val_explicit]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    norm_num [transUnit, transMat, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]

/-- The printed group element `[[2ᵏ A, v], [0, 1]]`. -/
def aff (k : ℤ) (A : SL3) (q : Fin 3 → ℚ) : Matˣ := affUnit A q * dU ^ k

/-- **The printed matrix of the remark**, entry by entry:
`[[2ᵏ A, v], [0, 1]]` with `A ∈ SL₃(ℤ)` and last column `v`. -/
def printedMat (k : ℤ) (A : SL3) (v : Fin 3 → ℚ) : Mat :=
  !![(2 : ℚ) ^ k * ((A : Matrix (Fin 3) (Fin 3) ℤ) 0 0 : ℚ),
      (2 : ℚ) ^ k * ((A : Matrix (Fin 3) (Fin 3) ℤ) 0 1 : ℚ),
      (2 : ℚ) ^ k * ((A : Matrix (Fin 3) (Fin 3) ℤ) 0 2 : ℚ), v 0;
    (2 : ℚ) ^ k * ((A : Matrix (Fin 3) (Fin 3) ℤ) 1 0 : ℚ),
      (2 : ℚ) ^ k * ((A : Matrix (Fin 3) (Fin 3) ℤ) 1 1 : ℚ),
      (2 : ℚ) ^ k * ((A : Matrix (Fin 3) (Fin 3) ℤ) 1 2 : ℚ), v 1;
    (2 : ℚ) ^ k * ((A : Matrix (Fin 3) (Fin 3) ℤ) 2 0 : ℚ),
      (2 : ℚ) ^ k * ((A : Matrix (Fin 3) (Fin 3) ℤ) 2 1 : ℚ),
      (2 : ℚ) ^ k * ((A : Matrix (Fin 3) (Fin 3) ℤ) 2 2 : ℚ), v 2;
    0, 0, 0, 1]

set_option linter.unusedSimpArgs false in
theorem aff_val (k : ℤ) (A : SL3) (q : Fin 3 → ℚ) :
    ((aff k A q : Matˣ) : Mat) = printedMat k A q := by
  refine Matrix.ext fun i j => ?_
  rw [aff, Units.val_mul, affUnit_val, dU_zpow_val, Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    norm_num [printedMat, dScale, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons] <;>
    ring

set_option linter.unusedSimpArgs false in
/-- **Conjugating by `Dᵐ` divides the translation part by `2ᵐ`.** -/
theorem dU_zpow_conj (m : ℤ) (A : SL3) (q : Fin 3 → ℚ) :
    (dU ^ m)⁻¹ * affUnit A q * dU ^ m =
      affUnit A (fun i => (2 : ℚ) ^ (-m) * q i) := by
  have h2 : ((2 : ℚ) ^ m) ≠ 0 := two_zpow_ne_zero m
  have hinv : ((dU ^ m : Matˣ)⁻¹ : Matˣ) = dU ^ (-m) := (_root_.zpow_neg dU m).symm
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, hinv, dU_zpow_val, dU_zpow_val,
    affUnit_val, affUnit_val]
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;>
    norm_num [dScale, _root_.zpow_neg, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons] <;>
    field_simp

/-- The same conjugation, with the target vector supplied by hand.  This is the
form the two image inclusions use: it never asks a rewrite to match a
beta-reduced lambda. -/
theorem dU_zpow_conj' (m : ℤ) (A : SL3) (q v : Fin 3 → ℚ)
    (h : ∀ i, v i = (2 : ℚ) ^ (-m) * q i) :
    (dU ^ m)⁻¹ * affUnit A q * dU ^ m = affUnit A v := by
  rw [dU_zpow_conj]
  congr 1
  funext i
  exact (h i).symm

/-! ## The affine normal form of the base `Γ̄` -/

/-- **Every element of `Γ̄` is affine**: `u = [[A, w], [0,1]]` with
`A ∈ SL₃(ℤ)` and `w ∈ ℤ³`.  This is the affine normal form carried by
completeness of the twenty-relator base presentation. -/
theorem gammaBar_affUnit_form {u : Matˣ} (hu : u ∈ gammaBar) :
    ∃ (w : Fin 3 → ℤ) (A : SL3), u = affUnit A (fun i => (w i : ℚ)) := by
  obtain ⟨g, hg⟩ := LiteralBaseAffineQuotient.affineQuotient_surjective ⟨u, hu⟩
  set ρ : LiteralNonMFPresentation.Base :=
    LiteralBaseRotationRetract.rotationToBase
      (LiteralBaseRotationRetract.baseToRotation g) with hρdef
  have hτmem : g * ρ⁻¹ ∈ LiteralBaseTranslationNormal.translations := by
    rw [← LiteralBaseRotationRetract.baseToRotation_ker_eq_translations,
      MonoidHom.mem_ker, map_mul, map_inv, hρdef]
    have hσ : LiteralBaseRotationRetract.baseToRotation
        (LiteralBaseRotationRetract.rotationToBase
          (LiteralBaseRotationRetract.baseToRotation g)) =
        LiteralBaseRotationRetract.baseToRotation g :=
      DFunLike.congr_fun
        LiteralBaseRotationRetract.baseToRotation_comp_rotationToBase
        (LiteralBaseRotationRetract.baseToRotation g)
    rw [hσ, mul_inv_cancel]
  obtain ⟨a, b, c, habc⟩ := exists_translation_form hτmem
  obtain ⟨p, hp⟩ := LiteralBaseP13RotationQuotient.p13ToRotation_surjective
    (LiteralBaseRotationRetract.baseToRotation g)
  refine ⟨![a, b, c], toSL3 p, ?_⟩
  have hρval : ((LiteralBaseAffineQuotient.affineQuotient ρ : gammaBar) : Matˣ) =
      blockEmbed4 (toSL3 p) := by
    rw [hρdef, ← hp, affineQuotient_rotationToBase]
    have hcomp := DFunLike.congr_fun rotationToMat_comp_p13ToRotation p
    simpa only [MonoidHom.comp_apply] using hcomp
  have hτval :
      ((LiteralBaseAffineQuotient.affineQuotient (g * ρ⁻¹) : gammaBar) : Matˣ) =
        v1U ^ a * v2U ^ b * v3U ^ c := by
    rw [habc]
    have h1 : LiteralBaseAffineQuotient.affineQuotient
        LiteralBaseRelations.v1 = v1G := by
      show LiteralBaseAffineQuotient.affineQuotient
        (PresentedGroup.of LiteralNonMFPresentation.v1Index) = v1G
      rw [LiteralBaseAffineQuotient.affineQuotient_generator,
        LiteralNonMFLinearWitness.matrixBaseGenerator_v1]
    have h2 : LiteralBaseAffineQuotient.affineQuotient
        LiteralBaseRelations.v2 = v2G := by
      show LiteralBaseAffineQuotient.affineQuotient
        (PresentedGroup.of LiteralNonMFPresentation.v2Index) = v2G
      rw [LiteralBaseAffineQuotient.affineQuotient_generator,
        LiteralNonMFLinearWitness.matrixBaseGenerator_v2]
    have h3 : LiteralBaseAffineQuotient.affineQuotient
        LiteralBaseRelations.v3 = v3G := by
      show LiteralBaseAffineQuotient.affineQuotient
        (PresentedGroup.of LiteralNonMFPresentation.v3Index) = v3G
      rw [LiteralBaseAffineQuotient.affineQuotient_generator,
        LiteralNonMFLinearWitness.matrixBaseGenerator_v3]
    rw [map_mul, map_mul, _root_.map_zpow, _root_.map_zpow,
      _root_.map_zpow, h1, h2, h3]
    simp only [MulMemClass.coe_mul, SubgroupClass.coe_zpow]
    rfl
  have hdecomp : u =
      ((LiteralBaseAffineQuotient.affineQuotient (g * ρ⁻¹) : gammaBar) : Matˣ) *
        ((LiteralBaseAffineQuotient.affineQuotient ρ : gammaBar) : Matˣ) := by
    rw [← MulMemClass.coe_mul, ← map_mul, show g * ρ⁻¹ * ρ = g by group, hg]
  have hfinal : affUnit (toSL3 p) (fun i => ((![a, b, c] : Fin 3 → ℤ) i : ℚ)) =
      v1U ^ a * v2U ^ b * v3U ^ c * blockEmbed4 (toSL3 p) := by
    rw [vprod_eq_transUnit, affUnit]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
  rw [hdecomp, hτval, hρval]
  exact hfinal.symm

/-- The translation unit of an integer vector lies in `Γ̄`. -/
theorem transUnit_mem_gammaBar (a b c : ℤ) :
    transUnit (a : ℚ) (b : ℚ) (c : ℚ) ∈ gammaBar := by
  rw [← vprod_eq_transUnit]
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _
      (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) a)
      (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) b))
    (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) c)

/-- **Every `A ∈ SL₃(ℤ)` is realised inside `Γ̄`**, because the three printed
rotation letters generate `SL₃(ℤ)`. -/
theorem blockEmbed4_mem_gammaBar (A : SL3) :
    (blockEmbed4 A : Matˣ) ∈ gammaBar := by
  obtain ⟨p, hp⟩ := SL3ElementaryGeneration.toSL3_surjective A
  have h1 : ((LiteralBaseAffineQuotient.affineQuotient
      (LiteralBaseRotationRetract.rotationToBase
        (LiteralBaseP13RotationQuotient.p13ToRotation p)) : gammaBar) : Matˣ) =
      blockEmbed4 A := by
    rw [affineQuotient_rotationToBase, ← hp]
    have hcomp := DFunLike.congr_fun rotationToMat_comp_p13ToRotation p
    simpa only [MonoidHom.comp_apply] using hcomp
  rw [← h1]
  exact (LiteralBaseAffineQuotient.affineQuotient
    (LiteralBaseRotationRetract.rotationToBase
      (LiteralBaseP13RotationQuotient.p13ToRotation p))).2

theorem affUnit_mem_gammaBar (w : Fin 3 → ℤ) (A : SL3) :
    affUnit A (fun i => (w i : ℚ)) ∈ gammaBar :=
  Subgroup.mul_mem _ (transUnit_mem_gammaBar (w 0) (w 1) (w 2))
    (blockEmbed4_mem_gammaBar A)

/-! ## The realization homomorphism -/

theorem subtype_conjD (x : gammaBar) :
    gammaBar.subtype (conjD x) = dU * gammaBar.subtype x * dU⁻¹ := rfl

/-- **The printed realization** `V →* GL₄(ℚ)`: the inclusion of the base
`Γ̄ ≤ GL₄(ℚ)`, extended by sending the stable letter to `D = diag(2,2,2,1)`.
The extension exists because conjugation by `D` *is* the compressing
endomorphism `conjD`. -/
def realization : Vertical conjD conjD_injective →* Matˣ :=
  verticalLift conjD conjD_injective gammaBar.subtype dU subtype_conjD

theorem realization_iota (x : gammaBar) :
    realization (iotaVertical conjD conjD_injective x) = (x : Matˣ) :=
  verticalLift_iota conjD conjD_injective gammaBar.subtype dU subtype_conjD x

theorem realization_t :
    realization (tVertical conjD conjD_injective) = dU :=
  verticalLift_t conjD conjD_injective gammaBar.subtype dU subtype_conjD

theorem realization_inl_level (n : ℕ) (x : gammaBar) :
    realization (inl (MappingTelescope.level conjD conjD_injective n x)) =
      (dU ^ n)⁻¹ * (x : Matˣ) * dU ^ n :=
  verticalLift_inl_level conjD conjD_injective gammaBar.subtype dU
    subtype_conjD n x

theorem realization_inr (r : Multiplicative ℤ) :
    realization (inr r : Vertical conjD conjD_injective) =
      dU ^ (Multiplicative.toAdd r) := by
  have hpow : (inr r : Vertical conjD conjD_injective) =
      tVertical conjD conjD_injective ^ (Multiplicative.toAdd r) := by
    rw [tVertical, ← _root_.map_zpow]
    congr 1
    rw [← Int.ofAdd_mul, one_mul, ofAdd_toAdd]
  rw [hpow, _root_.map_zpow, realization_t]

theorem realization_split (n : ℕ) (x : gammaBar) (r : Multiplicative ℤ) :
    realization (⟨MappingTelescope.mk conjD conjD_injective n x, r⟩ :
        Vertical conjD conjD_injective) =
      (dU ^ (n : ℤ))⁻¹ * (x : Matˣ) * dU ^ (n : ℤ) *
        dU ^ (Multiplicative.toAdd r) := by
  have hsplit :
      (⟨MappingTelescope.mk conjD conjD_injective n x, r⟩ :
          Vertical conjD conjD_injective) =
        inl (MappingTelescope.level conjD conjD_injective n x) * inr r :=
    (SemidirectProduct.inl_left_mul_inr_right _).symm
  rw [hsplit, map_mul, realization_inl_level, realization_inr,
    ← zpow_natCast dU n]

/-! ## Faithfulness -/

/-- **The realization is faithful.**  The stable-letter exponent is caught by
integrality: a power `D⁻ᵏ` inside `Γ̄` has both `2⁻ᵏ` and `2ᵏ` integral, so
`k = 0`; the telescope part then cancels. -/
theorem realization_injective : Function.Injective realization := by
  rw [injective_iff_map_eq_one]
  rintro ⟨u, r⟩ hv
  obtain ⟨⟨n, x⟩, hnx⟩ := MappingTelescope.mk_surjective conjD conjD_injective u
  dsimp only at hnx
  subst hnx
  rw [realization_split] at hv
  set k : ℤ := Multiplicative.toAdd r with hkdef
  have h2 : (x : Matˣ) * (dU ^ (n : ℤ) * dU ^ k) = dU ^ (n : ℤ) := by
    have h3 := congrArg (fun w : Matˣ => dU ^ (n : ℤ) * w) hv
    simpa [mul_assoc] using h3
  have hx : (x : Matˣ) = dU ^ (-k) := by
    rw [← _root_.zpow_add] at h2
    have h4 : (x : Matˣ) = dU ^ (n : ℤ) * (dU ^ ((n : ℤ) + k))⁻¹ :=
      eq_mul_inv_of_mul_eq h2
    rw [h4, ← _root_.zpow_neg, ← _root_.zpow_add]
    congr 1
    ring
  have hxint : IsIntegralUnit (dU ^ (-k)) := by
    rw [← hx]
    exact gammaBar_isIntegralUnit x.2
  have e1 : ((dU ^ (-k) : Matˣ) : Mat) 0 0 = (2 : ℚ) ^ (-k) := by
    rw [dU_zpow_val]
    simp [dScale]
  have e2 : (((dU ^ (-k) : Matˣ)⁻¹ : Matˣ) : Mat) 0 0 = (2 : ℚ) ^ k := by
    rw [← _root_.zpow_neg, neg_neg, dU_zpow_val]
    simp [dScale]
  obtain ⟨m1, hm1⟩ := hxint.1 0 0
  obtain ⟨m2, hm2⟩ := hxint.2 0 0
  rw [e1] at hm1
  rw [e2] at hm2
  have hm1' : (m1 : ℚ) = (2 : ℚ) ^ (-k) := by simpa using hm1
  have hm2' : (m2 : ℚ) = (2 : ℚ) ^ k := by simpa using hm2
  have hprod : m1 * m2 = 1 := by
    have hq : ((m1 * m2 : ℤ) : ℚ) = 1 := by
      push_cast
      rw [hm1', hm2', ← zpow_add₀ (show (2 : ℚ) ≠ 0 by norm_num)]
      simp
    exact_mod_cast hq
  have h20 : (0 : ℚ) ≤ 2 := by norm_num
  have h21 : (2 : ℚ) ≠ 1 := by norm_num
  have h22 : (0 : ℚ) < 2 := by norm_num
  have hk : k = 0 := by
    rcases Int.isUnit_iff.mp
        (IsUnit.of_mul_eq_one _ (show m2 * m1 = 1 by rw [mul_comm]; exact hprod)) with h | h
    · rw [h] at hm2'
      have hone : (2 : ℚ) ^ k = 1 := by exact_mod_cast hm2'.symm
      exact (zpow_eq_one_iff_right₀ h20 h21).mp hone
    · exfalso
      have hpos : (0 : ℚ) < (2 : ℚ) ^ k := zpow_pos h22 k
      rw [← hm2', h] at hpos
      norm_num at hpos
  have hx1 : x = 1 := by
    apply Subtype.ext
    rw [hx, hk]
    simp
  refine SemidirectProduct.ext ?_ ?_
  · show MappingTelescope.mk conjD conjD_injective n x = 1
    rw [hx1, ← MappingTelescope.one_eq_mk conjD conjD_injective n]
  · show r = 1
    exact _root_.toAdd_eq_zero.mp (hkdef.symm.trans hk)

/-! ## The printed image -/

/-- **The printed set** of the remark:
`{ [[2ᵏ A, v], [0, 1]] : A ∈ SL₃(ℤ), v ∈ ℤ[1/2]³, k ∈ ℤ }`, where `ℤ[1/2]` is
`DyadicRationals.dyadicSubring`. -/
def printedRealization : Set Matˣ :=
  {u | ∃ (k : ℤ) (A : SL3) (v : Fin 3 → ℚ),
        (∀ i, v i ∈ dyadicSubring) ∧ (u : Mat) = printedMat k A v}

theorem dyadic_raise {q : ℚ} {a : ℤ} {m d : ℕ} (h : q = (a : ℚ) / 2 ^ m) :
    q = ((a * 2 ^ d : ℤ) : ℚ) / 2 ^ (m + d) := by
  have h2 : ((2 : ℚ) ^ m) ≠ 0 := by positivity
  have h3 : ((2 : ℚ) ^ d) ≠ 0 := by positivity
  rw [h, pow_add]
  push_cast
  field_simp
  try ring

/-- Three dyadic rationals share a denominator `2ⁿ`. -/
theorem exists_common_denominator (v : Fin 3 → ℚ)
    (hv : ∀ i, v i ∈ dyadicSubring) :
    ∃ (n : ℕ) (w : Fin 3 → ℤ), ∀ i, v i = (w i : ℚ) / 2 ^ n := by
  obtain ⟨a0, n0, h0⟩ := mem_dyadicSubring.mp (hv 0)
  obtain ⟨a1, n1, h1⟩ := mem_dyadicSubring.mp (hv 1)
  obtain ⟨a2, n2, h2⟩ := mem_dyadicSubring.mp (hv 2)
  have k0 : n0 ≤ max n0 (max n1 n2) := le_max_left _ _
  have k1 : n1 ≤ max n0 (max n1 n2) :=
    le_trans (le_max_left _ _) (le_max_right n0 (max n1 n2))
  have k2 : n2 ≤ max n0 (max n1 n2) :=
    le_trans (le_max_right _ _) (le_max_right n0 (max n1 n2))
  have r0 := dyadic_raise (d := max n0 (max n1 n2) - n0) h0
  have r1 := dyadic_raise (d := max n0 (max n1 n2) - n1) h1
  have r2 := dyadic_raise (d := max n0 (max n1 n2) - n2) h2
  rw [Nat.add_sub_cancel' k0] at r0
  rw [Nat.add_sub_cancel' k1] at r1
  rw [Nat.add_sub_cancel' k2] at r2
  refine ⟨max n0 (max n1 n2),
    ![a0 * 2 ^ (max n0 (max n1 n2) - n0), a1 * 2 ^ (max n0 (max n1 n2) - n1),
      a2 * 2 ^ (max n0 (max n1 n2) - n2)], ?_⟩
  intro i
  fin_cases i
  · simpa using r0
  · simpa using r1
  · simpa using r2

/-- **The image of the realization lies in the printed set.** -/
theorem realization_mem_printed (v : Vertical conjD conjD_injective) :
    realization v ∈ printedRealization := by
  obtain ⟨u, r⟩ := v
  obtain ⟨⟨n, x⟩, hnx⟩ := MappingTelescope.mk_surjective conjD conjD_injective u
  dsimp only at hnx
  subst hnx
  obtain ⟨w, A, hA⟩ := gammaBar_affUnit_form x.2
  refine ⟨Multiplicative.toAdd r, A,
    fun i => (2 : ℚ) ^ (-(n : ℤ)) * (w i : ℚ), ?_, ?_⟩
  · intro i
    exact mem_dyadicSubring.mpr
      ⟨w i, n, by rw [_root_.zpow_neg, zpow_natCast, div_eq_mul_inv]; ring⟩
  · rw [realization_split, hA,
      dU_zpow_conj' (n : ℤ) A (fun i => (w i : ℚ))
        (fun i => (2 : ℚ) ^ (-(n : ℤ)) * (w i : ℚ)) fun _ => rfl]
    exact aff_val (Multiplicative.toAdd r) A _

/-- **The printed set lies in the image.** -/
theorem printed_subset_range :
    printedRealization ⊆ Set.range realization := by
  rintro u ⟨k, A, v, hv, hval⟩
  obtain ⟨n, w, hw⟩ := exists_common_denominator v hv
  have hx : affUnit A (fun i => (w i : ℚ)) ∈ gammaBar := affUnit_mem_gammaBar w A
  have hq : ∀ i, v i = (2 : ℚ) ^ (-(n : ℤ)) * (w i : ℚ) := by
    intro i
    rw [hw i, _root_.zpow_neg, zpow_natCast, div_eq_mul_inv]
    ring
  refine ⟨⟨MappingTelescope.mk conjD conjD_injective n
      ⟨affUnit A (fun i => (w i : ℚ)), hx⟩, Multiplicative.ofAdd k⟩, ?_⟩
  rw [realization_split]
  show (dU ^ (n : ℤ))⁻¹ * affUnit A (fun i => (w i : ℚ)) * dU ^ (n : ℤ) *
      dU ^ k = u
  rw [dU_zpow_conj' (n : ℤ) A (fun i => (w i : ℚ)) v hq]
  refine Units.ext ?_
  rw [hval]
  exact aff_val k A v

/-- **The image of the faithful realization is exactly the printed set.** -/
theorem range_realization : Set.range realization = printedRealization := by
  refine Set.Subset.antisymm ?_ printed_subset_range
  rintro _ ⟨v, rfl⟩
  exact realization_mem_printed v

/-! ## The printed sentence -/

/-- **The printed realization sentence** (`non_mf_groups_exist.tex`, the remark
after `prop:max-infinite`):

> The ascending HNN extension `V` of `ℤ³ ⋊ SL₃(ℤ)` along `(v,A) ↦ (2v,A)` has
> the faithful matrix realization
> `V ≅ { [[2ᵏ A, v], [0,1]] : A ∈ SL₃(ℤ), v ∈ ℤ[1/2]³, k ∈ ℤ }`. -/
theorem manuscriptSentence_ascendingHNNMatrixRealization :
    ∃ ρ : Manuscript.OneSidedMFRadical.MaxInfiniteConverse.V →*
        Matrix.GeneralLinearGroup (Fin 4) ℚ,
      Function.Injective ρ ∧ Set.range ρ = printedRealization :=
  ⟨realization, realization_injective, range_realization⟩

/-- The realization as the printed isomorphism `V ≅ {…}`. -/
def realizationEquiv :
    Manuscript.OneSidedMFRadical.MaxInfiniteConverse.V ≃* realization.range :=
  MonoidHom.ofInjective realization_injective

theorem coe_realization_range :
    (realization.range : Set Matˣ) = printedRealization := range_realization

/-- **The whole printed remark**, realization included: `V` satisfies the
hypothesis of `prop:max-infinite` (a property-(T) subgroup properly compressed
by the stable letter), it has the displayed faithful matrix realization, and it
is residually finite and MF. -/
def PrintedMaxInfiniteConverseRemarkWithRealization : Prop :=
  (HasKazhdanPropertyT.{0, 0}
      ↥Manuscript.OneSidedMFRadical.MaxInfiniteConverse.baseCopy ∧
    Manuscript.OneSidedMFRadical.MaxInfiniteConverse.baseCopy.map
        (MulAut.conj
          Manuscript.OneSidedMFRadical.MaxInfiniteConverse.stable).toMonoidHom <
      Manuscript.OneSidedMFRadical.MaxInfiniteConverse.baseCopy) ∧
  (∃ ρ : Manuscript.OneSidedMFRadical.MaxInfiniteConverse.V →*
      Matrix.GeneralLinearGroup (Fin 4) ℚ,
      Function.Injective ρ ∧ Set.range ρ = printedRealization) ∧
  Group.ResiduallyFinite Manuscript.OneSidedMFRadical.MaxInfiniteConverse.V ∧
  IsOperatorMF Manuscript.OneSidedMFRadical.MaxInfiniteConverse.V

theorem manuscriptMaxInfiniteConverseRemarkWithRealization :
    PrintedMaxInfiniteConverseRemarkWithRealization :=
  ⟨⟨Manuscript.OneSidedMFRadical.MaxInfiniteConverse.baseCopy_hasKazhdanPropertyT,
      Manuscript.OneSidedMFRadical.MaxInfiniteConverse.baseCopy_conj_lt⟩,
    ⟨realization, realization_injective, range_realization⟩,
    Manuscript.OneSidedMFRadical.MaxInfiniteConverse.residuallyFinite,
    Manuscript.OneSidedMFRadical.MaxInfiniteConverse.isOperatorMF⟩

end

end AffineHNNBase
end GroupApproximation

open GroupApproximation

#audit_closed_axioms
  AffineHNNBase.manuscriptSentence_ascendingHNNMatrixRealization
#audit_closed_axioms
  AffineHNNBase.manuscriptMaxInfiniteConverseRemarkWithRealization
