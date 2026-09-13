import GroupApproximation.Leavitt.ElementaryGroup
import Mathlib.Data.Matrix.Basis
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Center

/-!
# The centre of `EL_ι(R)`, and infiniteness of `EL_ι(R)/Z`

The Pestov 9.1 witness is `S = EL₃(R)/Z(EL₃(R))` over `R = LC(X, 𝔽_q) ⋊ ℤ`.
This module computes the centre far enough for every lane, over an arbitrary
unital ring `R` and any index type with two distinct indices.

1. **Central elements are scalar over central units.**  A matrix commuting
   with every `x_{ij}(1)` is scalar, `c • 1`; commuting with every `x_{ij}(r)`
   forces `r c = c r`; and `c` is a unit because the inverse is scalar too.

2. **Trivial centre.**  If the only central unit of `R` is `1` -- in
   particular if every central element of `R` is `0` or `1` -- then
   `Z(EL_ι(R)) = ⊥` and `EL_ι(R)/Z ≃* EL_ι(R)`.  For the witness `Z(R) = 𝔽_q`
   by freeness and minimality, so at `q = 2` the quotient disappears and
   `S = EL₃(R)` for every lane.

3. **Infiniteness and nontriviality.**  `x_{ij}(a)` is central only for
   `a = 0`, so `a ↦ [x_{ij}(a)]` is injective into `EL_ι(R)/Z`.  The quotient
   is infinite whenever `R` is, and nontrivial whenever `R` is.  This needs no
   bound on the centre.
-/

namespace GroupApproximation
namespace Pestov91

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- A central element of `EL_ι(R)` commutes, as a matrix, with every `E_{ij}(a)`. -/
theorem single_mul_eq_mul_single_of_mem_center
    {g : ↥(elementaryGroup ι R)} (hg : g ∈ Subgroup.center ↥(elementaryGroup ι R))
    (i j : ι) (h : i ≠ j) (a : R) :
    Matrix.single i j a * ((g : (Matrix ι ι R)ˣ) : Matrix ι ι R) =
      ((g : (Matrix ι ι R)ˣ) : Matrix ι ι R) * Matrix.single i j a := by
  have hc := Subgroup.mem_center_iff.mp hg ⟨elementaryUnit i j h a, elementaryUnit_mem i j h a⟩
  have hm : (1 + Matrix.single i j a) * ((g : (Matrix ι ι R)ˣ) : Matrix ι ι R) =
      ((g : (Matrix ι ι R)ˣ) : Matrix ι ι R) * (1 + Matrix.single i j a) :=
    congrArg (fun z : ↥(elementaryGroup ι R) ↦ ((z : (Matrix ι ι R)ˣ) : Matrix ι ι R)) hc
  rw [add_mul, mul_add, one_mul, mul_one] at hm
  exact add_left_cancel hm

/-- **Central elements of `EL_ι(R)` are scalar over the centre of `R`.** -/
theorem exists_central_scalar_of_mem_center [Nontrivial ι]
    {g : ↥(elementaryGroup ι R)} (hg : g ∈ Subgroup.center ↥(elementaryGroup ι R)) :
    ∃ c : R, (∀ r : R, r * c = c * r) ∧
      ((g : (Matrix ι ι R)ˣ) : Matrix ι ι R) = Matrix.scalar ι c := by
  have hsc : ((g : (Matrix ι ι R)ˣ) : Matrix ι ι R) ∈ Set.range (Matrix.scalar ι) := by
    refine Matrix.mem_range_scalar_of_commute_single ?_
    intro i j hij
    exact single_mul_eq_mul_single_of_mem_center hg i j hij 1
  obtain ⟨c, hc⟩ := hsc
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  refine ⟨c, fun r ↦ ?_, hc.symm⟩
  have hr := single_mul_eq_mul_single_of_mem_center hg i j hij r
  rw [← hc] at hr
  simpa [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul] using
    congrFun (congrFun hr i) j

/-- **`Z(EL_ι(R))` consists of scalars over central units of `R`.** -/
theorem exists_central_unit_scalar_of_mem_center [Nontrivial ι]
    {g : ↥(elementaryGroup ι R)} (hg : g ∈ Subgroup.center ↥(elementaryGroup ι R)) :
    ∃ c : R, (∀ r : R, r * c = c * r) ∧ IsUnit c ∧
      ((g : (Matrix ι ι R)ˣ) : Matrix ι ι R) = Matrix.scalar ι c := by
  obtain ⟨c, hc, hM⟩ := exists_central_scalar_of_mem_center hg
  obtain ⟨d, -, hN⟩ := exists_central_scalar_of_mem_center (inv_mem hg)
  obtain ⟨i, -⟩ := exists_pair_ne ι
  have h1 : ((g : (Matrix ι ι R)ˣ) : Matrix ι ι R) *
      (((g⁻¹ : ↥(elementaryGroup ι R)) : (Matrix ι ι R)ˣ) : Matrix ι ι R) = 1 := by
    rw [Subgroup.coe_inv, Units.mul_inv]
  have h2 : (((g⁻¹ : ↥(elementaryGroup ι R)) : (Matrix ι ι R)ˣ) : Matrix ι ι R) *
      ((g : (Matrix ι ι R)ˣ) : Matrix ι ι R) = 1 := by
    rw [Subgroup.coe_inv, Units.inv_mul]
  rw [hM, hN] at h1 h2
  have hcd : c * d = 1 := by
    simpa [Matrix.scalar_apply] using congrFun (congrFun h1 i) i
  have hdc : d * c = 1 := by
    simpa [Matrix.scalar_apply] using congrFun (congrFun h2 i) i
  exact ⟨c, hc, ⟨⟨c, d, hcd, hdc⟩, rfl⟩, hM⟩

/-- **Trivial centre.**  If `1` is the only central unit of `R`, then
`EL_ι(R)` has trivial centre. -/
theorem center_elementaryGroup_eq_bot [Nontrivial ι]
    (hR : ∀ c : R, (∀ r : R, r * c = c * r) → IsUnit c → c = 1) :
    Subgroup.center ↥(elementaryGroup ι R) = ⊥ := by
  refine eq_bot_iff.mpr ?_
  intro g hg
  rw [Subgroup.mem_bot]
  obtain ⟨c, hc, hu, hM⟩ := exists_central_unit_scalar_of_mem_center hg
  obtain rfl := hR c hc hu
  apply Subtype.ext
  apply Units.ext
  rw [hM]
  simp

/-- **Trivial centre when `Z(R) = {0, 1}`.**  This is the case `q = 2` of the
witness ring, whose centre is `𝔽_q`. -/
theorem center_elementaryGroup_eq_bot_of_central_zero_or_one [Nontrivial ι]
    (hR : ∀ c : R, (∀ r : R, r * c = c * r) → c = 0 ∨ c = 1) :
    Subgroup.center ↥(elementaryGroup ι R) = ⊥ := by
  refine center_elementaryGroup_eq_bot fun c hc hu ↦ ?_
  rcases hR c hc with rfl | rfl
  · exact isUnit_zero_iff.mp hu
  · rfl

/-- When `Z(R) = {0, 1}`, the quotient by the centre is `EL_ι(R)` itself. -/
noncomputable def elementaryModCentreEquiv [Nontrivial ι]
    (hR : ∀ c : R, (∀ r : R, r * c = c * r) → c = 0 ∨ c = 1) :
    (↥(elementaryGroup ι R) ⧸ Subgroup.center ↥(elementaryGroup ι R)) ≃*
      ↥(elementaryGroup ι R) :=
  (QuotientGroup.quotientMulEquivOfEq
    (center_elementaryGroup_eq_bot_of_central_zero_or_one hR)).trans
    QuotientGroup.quotientBot

/-- An elementary matrix `x_{ij}(a)` is central in `EL_ι(R)` exactly when `a = 0`. -/
theorem elementaryUnit_mem_center_iff (i j : ι) (h : i ≠ j) (a : R) :
    (⟨elementaryUnit i j h a, elementaryUnit_mem i j h a⟩ : ↥(elementaryGroup ι R)) ∈
      Subgroup.center ↥(elementaryGroup ι R) ↔ a = 0 := by
  constructor
  · intro hg
    have hm := single_mul_eq_mul_single_of_mem_center hg j i h.symm 1
    change Matrix.single j i 1 * (1 + Matrix.single i j a) =
      (1 + Matrix.single i j a) * Matrix.single j i 1 at hm
    rw [mul_add, add_mul, mul_one, one_mul, Matrix.single_mul_single_same,
      Matrix.single_mul_single_same] at hm
    simpa [Matrix.single_apply, h, h.symm] using congrFun (congrFun hm j) j
  · rintro rfl
    have h1 : (⟨elementaryUnit i j h 0, elementaryUnit_mem i j h 0⟩ :
        ↥(elementaryGroup ι R)) = 1 :=
      Subtype.ext (elementaryUnit_zero i j h)
    rw [h1]
    exact (Subgroup.center _).one_mem

/-- **`EL_ι(R)/Z(EL_ι(R))` is infinite** for every infinite ring `R`:
`a ↦ [x_{ij}(a)]` is injective. -/
theorem elementaryModCentre_infinite [Infinite R] (i j : ι) (h : i ≠ j) :
    Infinite (↥(elementaryGroup ι R) ⧸ Subgroup.center ↥(elementaryGroup ι R)) := by
  refine Infinite.of_injective
    (fun a : R ↦ ((⟨elementaryUnit i j h a, elementaryUnit_mem i j h a⟩ :
      ↥(elementaryGroup ι R)) :
        ↥(elementaryGroup ι R) ⧸ Subgroup.center ↥(elementaryGroup ι R))) ?_
  intro a b hab
  have hmem := QuotientGroup.eq.mp hab
  have hinv : (elementaryUnit i j h a)⁻¹ = elementaryUnit i j h (-a) :=
    inv_eq_of_mul_eq_one_right (by rw [elementaryUnit_mul, add_neg_cancel, elementaryUnit_zero])
  have hprod : ((⟨elementaryUnit i j h a, elementaryUnit_mem i j h a⟩ :
        ↥(elementaryGroup ι R))⁻¹ *
        ⟨elementaryUnit i j h b, elementaryUnit_mem i j h b⟩ : ↥(elementaryGroup ι R)) =
      ⟨elementaryUnit i j h (-a + b), elementaryUnit_mem i j h (-a + b)⟩ :=
    Subtype.ext (show (elementaryUnit i j h a)⁻¹ * elementaryUnit i j h b =
      elementaryUnit i j h (-a + b) by rw [hinv, elementaryUnit_mul])
  rw [hprod] at hmem
  exact neg_add_eq_zero.mp ((elementaryUnit_mem_center_iff i j h (-a + b)).mp hmem)

/-- **`EL_ι(R)/Z(EL_ι(R))` is nontrivial** for every nontrivial ring `R`. -/
theorem elementaryModCentre_nontrivial [Nontrivial R] (i j : ι) (h : i ≠ j) :
    Nontrivial (↥(elementaryGroup ι R) ⧸ Subgroup.center ↥(elementaryGroup ι R)) := by
  refine nontrivial_of_ne
    ((⟨elementaryUnit i j h 1, elementaryUnit_mem i j h 1⟩ : ↥(elementaryGroup ι R)) :
      ↥(elementaryGroup ι R) ⧸ Subgroup.center ↥(elementaryGroup ι R)) 1 ?_
  intro h1
  exact one_ne_zero
    ((elementaryUnit_mem_center_iff i j h 1).mp ((QuotientGroup.eq_one_iff _).mp h1))

/-! ### Model tests

The trivial-centre hypothesis is satisfiable (`𝔽₂`) and not vacuous (`𝔽₃`
fails it), and infiniteness of the quotient has an instance at `ℤ`. -/

/-- `𝔽₂` satisfies the trivial-centre hypothesis. -/
theorem zmod2_central_zero_or_one :
    ∀ c : ZMod 2, (∀ r : ZMod 2, r * c = c * r) → c = 0 ∨ c = 1 := by
  intro c _
  fin_cases c
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- `Z(EL₃(𝔽₂)) = ⊥`. -/
theorem center_elementaryGroup_zmod2_eq_bot :
    Subgroup.center ↥(elementaryGroup (Fin 3) (ZMod 2)) = ⊥ :=
  center_elementaryGroup_eq_bot_of_central_zero_or_one zmod2_central_zero_or_one

/-- `𝔽₃` fails the trivial-centre hypothesis: `2` is central. -/
theorem not_central_zero_or_one_zmod3 :
    ¬ ∀ c : ZMod 3, (∀ r : ZMod 3, r * c = c * r) → c = 0 ∨ c = 1 := by
  intro hR
  rcases hR 2 fun r ↦ mul_comm r 2 with h2 | h2
  · exact absurd h2 (by decide)
  · exact absurd h2 (by decide)

/-- `EL₃(ℤ)/Z(EL₃(ℤ))` is infinite. -/
theorem intElementaryModCentre_infinite :
    Infinite (↥(elementaryGroup (Fin 3) ℤ) ⧸ Subgroup.center ↥(elementaryGroup (Fin 3) ℤ)) :=
  elementaryModCentre_infinite (0 : Fin 3) 1 (by decide)

end Pestov91
end GroupApproximation
