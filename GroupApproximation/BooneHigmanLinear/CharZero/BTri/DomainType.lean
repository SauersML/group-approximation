import GroupApproximation.BooneHigmanLinear.CharZero.BTri.Action
import Mathlib.LinearAlgebra.Matrix.SemiringInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Data.ZMod.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Z.3, part 1: the type of a vertex of the Ã₂ building

Lane `fix-bh-a`, piece Z.3 of the Z1-base route (board `k2-poly.md`; model `BTri/Building.lean`).
Here `A` is a domain, `p ∈ A` is prime and `B = A[1/p]` (`IsLocalization.Away p B`).

* `exists_unit_decomp`: every unit of `B` is `v · p^n` with `v ∈ Aˣ` and `n ∈ ℤ`.  The exponent is
  unique (`exp_unique`), which defines the valuation `pval : Bˣ → ℤ` (`pval_mul`, `pval_map`,
  `pval_pUnit`).
* `exists_eq_mul_map_of_latOf_eq`: two matrices in `GL₃(B)` with the same column lattice differ
  by right multiplication by `GL₃(A)`.  Conversely `latOf_mul_map` holds.
* `smul_latOf`: `p^a • latOf g = latOf (p^a g)`.
* `detVal g = pval (det g)` and **`vertexType : Vertex A B p → ZMod 3`**, the class of
  `detVal g` mod 3.  It is well defined on homothety classes (`detVal_homothetic`): changing the
  basis changes `detVal` by `0`, and scaling by `p^a` changes it by `3a`.

The action-dependent part (invariance under `SL₃(B)` and the classification of vertices) is in
`DomainVertex.lean`, on top of `BTri/Action.lean`.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace BTri

open scoped Pointwise
open Matrix

section Units

variable {A : Type*} [CommRing A] [IsDomain A] {B : Type*} [CommRing B] [Algebra A B]
  (p : A) [IsLocalization.Away p B]

/-- `p` as a unit of `B = A[1/p]`. -/
noncomputable def pU : Bˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := B) p).unit

omit [IsDomain A] in
@[simp] theorem coe_pU : ((pU (B := B) p : Bˣ) : B) = algebraMap A B p :=
  IsUnit.unit_spec _

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.coe_pU

/-- The units of `A` inside `B`. -/
noncomputable def unitsMap : Aˣ →* Bˣ :=
  Units.map (algebraMap A B).toMonoidHom

omit [IsDomain A] in
@[simp] theorem coe_unitsMap (v : Aˣ) : ((unitsMap (B := B) v : Bˣ) : B) = algebraMap A B v :=
  rfl

variable {p}

theorem algebraMap_injective (hp : Prime p) : Function.Injective (algebraMap A B) :=
  IsLocalization.injective B (powers_le_nonZeroDivisors_of_noZeroDivisors hp.ne_zero)

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.algebraMap_injective

/-- **Units of `A[1/p]`**: every unit is `v p^n` with `v ∈ Aˣ`, `n ∈ ℤ`. -/
theorem exists_unit_decomp (hp : Prime p) (u : Bˣ) :
    ∃ (v : Aˣ) (n : ℤ), u = unitsMap v * pU (B := B) p ^ n := by
  obtain ⟨⟨a, s⟩, h1⟩ := IsLocalization.surj (Submonoid.powers p) (u : B)
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
  obtain ⟨⟨c, t⟩, h2⟩ := IsLocalization.surj (Submonoid.powers p) ((u⁻¹ : Bˣ) : B)
  obtain ⟨l, hl⟩ := (Submonoid.mem_powers_iff _ _).mp t.2
  simp only at h1 h2
  rw [← hk] at h1
  rw [← hl] at h2
  have key : a * c = p ^ (k + l) := by
    apply algebraMap_injective (B := B) hp
    rw [map_mul, ← h1, ← h2, pow_add, map_mul]
    calc (u : B) * algebraMap A B (p ^ k) * (((u⁻¹ : Bˣ) : B) * algebraMap A B (p ^ l)) =
        ((u : B) * ((u⁻¹ : Bˣ) : B)) * (algebraMap A B (p ^ k) * algebraMap A B (p ^ l)) := by
          ring
      _ = algebraMap A B (p ^ k) * algebraMap A B (p ^ l) := by rw [Units.mul_inv, one_mul]
  obtain ⟨i, -, w, hw⟩ := (dvd_prime_pow hp (k + l)).mp ⟨c, key.symm⟩
  have ha : a = p ^ i * ((w⁻¹ : Aˣ) : A) := by
    rw [← hw, mul_assoc, Units.mul_inv, mul_one]
  have e : u * pU (B := B) p ^ k = unitsMap w⁻¹ * pU (B := B) p ^ i := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, coe_pU, coe_unitsMap]
    rw [← map_pow, h1, ha, map_mul, map_pow]
    ring
  refine ⟨w⁻¹, (i : ℤ) - k, ?_⟩
  rw [zpow_sub, zpow_natCast, zpow_natCast, ← mul_assoc, ← e, mul_inv_cancel_right]

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.exists_unit_decomp

/-- A nonnegative exponent that is absorbed by `Aˣ` is zero. -/
theorem nat_exp_eq_zero (hp : Prime p) {v v' : Aˣ} {j : ℕ}
    (h : unitsMap (B := B) v * pU (B := B) p ^ j = unitsMap v') : j = 0 := by
  have hA : (v : A) * p ^ j = v' := by
    apply algebraMap_injective (B := B) hp
    have := congrArg Units.val h
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, coe_pU, coe_unitsMap] at this
    rw [map_mul, map_pow, this]
  have hu : IsUnit (p ^ j) := by
    have : p ^ j = ((v⁻¹ : Aˣ) : A) * v' := by
      rw [← hA, ← mul_assoc, Units.inv_mul, one_mul]
    rw [this]
    exact (Units.isUnit _).mul (Units.isUnit _)
  exact (isUnit_pow_iff_of_not_isUnit hp.not_unit).mp hu

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.nat_exp_eq_zero

/-- **Uniqueness of the exponent** in `v p^n`. -/
theorem exp_unique (hp : Prime p) {v v' : Aˣ} {n m : ℤ}
    (h : unitsMap (B := B) v * pU (B := B) p ^ n = unitsMap v' * pU (B := B) p ^ m) : n = m := by
  obtain ⟨j, hj | hj⟩ := Int.eq_nat_or_neg (n - m)
  · have e : unitsMap (B := B) v * pU (B := B) p ^ j = unitsMap v' := by
      rw [← zpow_natCast, ← hj, zpow_sub, ← mul_assoc, h, mul_inv_cancel_right]
    have := nat_exp_eq_zero hp e
    omega
  · have hj' : m - n = (j : ℤ) := by omega
    have e : unitsMap (B := B) v' * pU (B := B) p ^ j = unitsMap v := by
      rw [← zpow_natCast, ← hj', zpow_sub, ← mul_assoc, ← h, mul_inv_cancel_right]
    have := nat_exp_eq_zero hp e
    omega

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.exp_unique

/-- The `p`-adic valuation of a unit of `A[1/p]`. -/
noncomputable def pval (hp : Prime p) (u : Bˣ) : ℤ :=
  (exists_unit_decomp hp u).choose_spec.choose

theorem pval_spec (hp : Prime p) (u : Bˣ) :
    u = unitsMap (exists_unit_decomp hp u).choose * pU (B := B) p ^ pval hp u :=
  (exists_unit_decomp hp u).choose_spec.choose_spec

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.pval_spec

theorem pval_eq (hp : Prime p) {u : Bˣ} {v : Aˣ} {n : ℤ} (h : u = unitsMap v * pU (B := B) p ^ n) :
    pval hp u = n :=
  exp_unique hp ((pval_spec hp u).symm.trans h)

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.pval_eq

theorem pval_mul (hp : Prime p) (u w : Bˣ) : pval hp (u * w) = pval hp u + pval hp w := by
  apply pval_eq hp (v := (exists_unit_decomp hp u).choose * (exists_unit_decomp hp w).choose)
  conv_lhs => rw [pval_spec hp u, pval_spec hp w]
  rw [map_mul, zpow_add]
  exact mul_mul_mul_comm _ _ _ _

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.pval_mul

@[simp] theorem pval_map (hp : Prime p) (v : Aˣ) : pval hp (unitsMap (B := B) v) = 0 :=
  pval_eq hp (v := v) (by rw [zpow_zero, mul_one])

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.pval_map

@[simp] theorem pval_pU_pow (hp : Prime p) (n : ℤ) : pval hp (pU (B := B) p ^ n) = n :=
  pval_eq hp (v := 1) (by rw [map_one, one_mul])

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.pval_pU_pow

end Units

section Lattices

variable {A : Type*} [CommRing A] {B : Type*} [CommRing B] [Algebra A B] (p : A)

theorem col_mem_latOf (g : GL (Fin 3) B) (j : Fin 3) :
    (fun i => (g : Matrix (Fin 3) (Fin 3) B) i j) ∈ latOf A B g :=
  Submodule.subset_span ⟨j, rfl⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.col_mem_latOf

/-- A matrix `g K` with `K` over `A` has its column lattice inside that of `g`. -/
theorem latOf_le_of_eq_mul {g h : GL (Fin 3) B} {K : Matrix (Fin 3) (Fin 3) A}
    (e : (h : Matrix (Fin 3) (Fin 3) B) = (g : Matrix (Fin 3) (Fin 3) B) * K.map (algebraMap A B)) :
    latOf A B h ≤ latOf A B g := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨j, rfl⟩
  have hcol : (fun i => (h : Matrix (Fin 3) (Fin 3) B) i j) =
      ∑ l, K l j • fun i => (g : Matrix (Fin 3) (Fin 3) B) i l := by
    ext i
    show (h : Matrix (Fin 3) (Fin 3) B) i j = _
    rw [e, Matrix.mul_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Pi.smul_apply, Algebra.smul_def, Matrix.map_apply]
    ring
  show (fun i => (h : Matrix (Fin 3) (Fin 3) B) i j) ∈ (latOf A B g : Set (Fin 3 → B))
  rw [hcol]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (col_mem_latOf g l)

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.latOf_le_of_eq_mul

/-- Right multiplication by `GL₃(A)` does not change the column lattice. -/
theorem latOf_mul_map (g : GL (Fin 3) B) (k : GL (Fin 3) A) :
    latOf A B (g * Matrix.GeneralLinearGroup.map (algebraMap A B) k) = latOf A B g := by
  refine le_antisymm (latOf_le_of_eq_mul (K := (k : Matrix (Fin 3) (Fin 3) A)) rfl) ?_
  refine latOf_le_of_eq_mul (K := ((k⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)) ?_
  change (g : Matrix (Fin 3) (Fin 3) B) =
    (g : Matrix (Fin 3) (Fin 3) B) * (k : Matrix (Fin 3) (Fin 3) A).map (algebraMap A B) *
      ((k⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A).map (algebraMap A B)
  rw [mul_assoc, ← Matrix.map_mul, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.GeneralLinearGroup.coe_one, Matrix.map_one _ (map_zero _) (map_one _), mul_one]

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.latOf_mul_map

/-- A column of `h` lying in `latOf g` gives a column of a matrix `K` over `A` with `h = g K`. -/
theorem exists_eq_mul_of_latOf_le {g h : GL (Fin 3) B} (hle : latOf A B h ≤ latOf A B g) :
    ∃ K : Matrix (Fin 3) (Fin 3) A,
      (h : Matrix (Fin 3) (Fin 3) B) = (g : Matrix (Fin 3) (Fin 3) B) * K.map (algebraMap A B) := by
  have hj : ∀ j : Fin 3, ∃ c : Fin 3 → A,
      ∑ l, c l • (fun i => (g : Matrix (Fin 3) (Fin 3) B) i l) =
        fun i => (h : Matrix (Fin 3) (Fin 3) B) i j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun A).mp (hle (col_mem_latOf h j))
  choose c hc using hj
  refine ⟨Matrix.of fun l j => c j l, ?_⟩
  ext i j
  have hij := congrFun (hc j) i
  simp only [Finset.sum_apply, Pi.smul_apply] at hij
  simp only [Algebra.smul_def] at hij
  rw [← hij, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Matrix.map_apply, Matrix.of_apply]
  ring

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.exists_eq_mul_of_latOf_le

/-- **Two bases of one lattice differ by `GL₃(A)`.** -/
theorem exists_eq_mul_map_of_latOf_eq [IsDomain A] (hp : Prime p) [IsLocalization.Away p B]
    {g h : GL (Fin 3) B} (e : latOf A B g = latOf A B h) :
    ∃ k : GL (Fin 3) A, h = g * Matrix.GeneralLinearGroup.map (algebraMap A B) k := by
  obtain ⟨K, hK⟩ := exists_eq_mul_of_latOf_le e.symm.le
  obtain ⟨K', hK'⟩ := exists_eq_mul_of_latOf_le e.le
  have hinj : Function.Injective (algebraMap A B) := algebraMap_injective (B := B) hp
  have h1 : K' * K = 1 := by
    have e1 : (h : Matrix (Fin 3) (Fin 3) B) * (K' * K).map (algebraMap A B) =
        (h : Matrix (Fin 3) (Fin 3) B) * 1 := by
      rw [Matrix.map_mul, ← mul_assoc, ← hK', ← hK, mul_one]
    have e2 : (K' * K).map (algebraMap A B) = (1 : Matrix (Fin 3) (Fin 3) A).map (algebraMap A B) := by
      rw [Matrix.map_one _ (map_zero _) (map_one _)]
      have := congrArg (((h⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) * ·) e1
      simpa only [← mul_assoc, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.GeneralLinearGroup.coe_one, one_mul] using this
    exact Matrix.map_injective hinj e2
  have h2 : K * K' = 1 := mul_eq_one_comm.mp h1
  refine ⟨⟨K, K', h2, h1⟩, ?_⟩
  exact Matrix.GeneralLinearGroup.ext fun i j => by rw [hK]; rfl

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.exists_eq_mul_map_of_latOf_eq

/-- `p^a • latOf g` is the lattice of `p^a g`. -/
theorem smul_latOf [IsLocalization.Away p B] (a : ℕ) (g : GL (Fin 3) B) :
    (p ^ a) • latOf A B g =
      latOf A B (Matrix.GeneralLinearGroup.scalar (Fin 3) (pU (B := B) p ^ a) * g) := by
  rw [latOf_mul A B, Submodule.pointwise_smul_def]
  congr 1
  refine LinearMap.ext fun v => funext fun i => ?_
  rw [DistribSMul.toLinearMap_apply, Pi.smul_apply, Algebra.smul_def, map_pow (algebraMap A B)]
  simp only [glLin, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply,
    Matrix.GeneralLinearGroup.coe_scalar, Units.val_pow_eq_pow_val, coe_pU, Matrix.scalar_apply,
    Matrix.mulVec_diagonal]

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.smul_latOf

end Lattices

section VertexType

variable {A : Type*} [CommRing A] [IsDomain A] {B : Type*} [CommRing B] [Algebra A B]
  {p : A} [IsLocalization.Away p B]

/-- `v_p(det g)`. -/
noncomputable def detVal (hp : Prime p) (g : GL (Fin 3) B) : ℤ :=
  pval hp (Matrix.GeneralLinearGroup.det g)

theorem detVal_mul (hp : Prime p) (g h : GL (Fin 3) B) :
    detVal hp (g * h) = detVal hp g + detVal hp h := by
  unfold detVal
  rw [map_mul, pval_mul]

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.detVal_mul

theorem detVal_map (hp : Prime p) (k : GL (Fin 3) A) :
    detVal hp (Matrix.GeneralLinearGroup.map (algebraMap A B) k) = 0 := by
  have e : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap A B) k) =
      unitsMap (B := B) (Matrix.GeneralLinearGroup.det k) := by
    apply Units.ext
    change Matrix.det ((k : Matrix (Fin 3) (Fin 3) A).map (algebraMap A B)) =
      algebraMap A B (Matrix.det (k : Matrix (Fin 3) (Fin 3) A))
    exact (RingHom.map_det (algebraMap A B) _).symm
  rw [detVal, e, pval_map]

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.detVal_map

theorem detVal_scalar (hp : Prime p) (a : ℕ) :
    detVal hp (Matrix.GeneralLinearGroup.scalar (Fin 3) (pU (B := B) p ^ a)) = 3 * a := by
  rw [detVal, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, ← pow_mul, ← zpow_natCast,
    pval_pU_pow]
  push_cast
  ring

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.detVal_scalar

/-- Homothetic matrices have the same `detVal` modulo 3. -/
theorem detVal_homothetic (hp : Prime p) {g h : GL (Fin 3) B} (hgh : Homothetic A B p g h) :
    ∃ a b : ℕ, detVal hp g + 3 * a = detVal hp h + 3 * b := by
  obtain ⟨a, b, e⟩ := hgh
  rw [smul_latOf, smul_latOf] at e
  obtain ⟨k, hk⟩ := exists_eq_mul_map_of_latOf_eq p hp e
  refine ⟨a, b, ?_⟩
  have := congrArg (detVal hp) hk
  rw [detVal_mul, detVal_mul, detVal_mul, detVal_map, detVal_scalar, detVal_scalar] at this
  linarith

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.detVal_homothetic

/-- **The type of a vertex**: `v_p(det g)` mod 3. -/
noncomputable def vertexType (hp : Prime p) : Vertex A B p → ZMod 3 :=
  Quotient.lift (fun g => ((detVal hp g : ℤ) : ZMod 3)) fun g h hgh => by
    obtain ⟨a, b, e⟩ := detVal_homothetic hp hgh
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    exact ⟨(a : ℤ) - b, by push_cast; linarith⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.vertexType

@[simp] theorem vertexType_vertexOf (hp : Prime p) (g : GL (Fin 3) B) :
    vertexType hp (vertexOf A B p g) = ((detVal hp g : ℤ) : ZMod 3) :=
  rfl

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.vertexType_vertexOf

end VertexType

end BTri
end BooneHigmanLinear
end GroupApproximation
