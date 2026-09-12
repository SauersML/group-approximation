import GroupApproximation.Algebra.PermutationalWreath
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# The mod-two lamp group is linear over a field

The linearity clause of Section 54.2.  A mod-two lamp configuration is a
finitely supported function to `ℤ/2`, so it becomes a polynomial

`λ(f) = ∑ f(x) t_x`

in one variable per site, and the unitriangular matrix `[[1, λ(f)], [0, 1]]`
turns the pointwise group law into matrix multiplication.  Linear independence
of the variables makes the assignment injective, and passing to the fraction
field puts the whole lamp group inside `GL₂` of a field.

Together with `lamp_isAmenable`, `lamp_isResiduallyFinite` and `suppIn_finite`
this completes the tameness list Section 54.2 attributes to the kernel of the
split extension: locally finite, amenable, residually finite, and linear.
-/

namespace GroupApproximation

namespace LampLinear

open MvPolynomial

universe v

variable {S : Type v}

/-- The lamp group of mod-two lamps. -/
abbrev TwoLamp (S : Type v) : Type v := Lamp (Multiplicative (ZMod 2)) S

/-- The support of a lamp configuration, as a finite set. -/
noncomputable def supp (f : TwoLamp S) : Finset S := (f.2).toFinset

theorem mem_supp {f : TwoLamp S} {x : S} :
    x ∈ supp f ↔ f.toFun x ≠ 1 := Set.Finite.mem_toFinset _

/-- The polynomial of a lamp configuration: one variable per lit site. -/
noncomputable def lampPoly (f : TwoLamp S) : MvPolynomial S (ZMod 2) :=
  ∑ x ∈ supp f, C (Multiplicative.toAdd (f.toFun x)) * X x

/-- The polynomial may be computed over any finite set containing the
support. -/
theorem lampPoly_eq_sum (f : TwoLamp S) {T : Finset S} (hT : supp f ⊆ T) :
    lampPoly f = ∑ x ∈ T, C (Multiplicative.toAdd (f.toFun x)) * X x := by
  classical
  rw [lampPoly, ← Finset.sum_subset hT]
  intro x _ hx
  have hone : f.toFun x = 1 := by
    by_contra hcon
    exact hx (mem_supp.mpr hcon)
  rw [hone]
  show C (Multiplicative.toAdd (1 : Multiplicative (ZMod 2))) * X x = 0
  simp

theorem lampPoly_mul (f g : TwoLamp S) :
    lampPoly (f * g) = lampPoly f + lampPoly g := by
  classical
  set T : Finset S := supp f ∪ supp g ∪ supp (f * g) with hT
  have hf : supp f ⊆ T := by
    rw [hT]
    exact Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left
  have hg : supp g ⊆ T := by
    rw [hT]
    exact Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left
  have hfg : supp (f * g) ⊆ T := by
    rw [hT]
    exact Finset.subset_union_right
  rw [lampPoly_eq_sum f hf, lampPoly_eq_sum g hg, lampPoly_eq_sum (f * g) hfg,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hval : Multiplicative.toAdd ((f * g).toFun x)
      = Multiplicative.toAdd (f.toFun x) + Multiplicative.toAdd (g.toFun x) := by
    rw [Lamp.mul_apply]
    rfl
  rw [hval, map_add, add_mul]

/-- Reading off one coefficient recovers one lamp value. -/
theorem coeff_lampPoly (f : TwoLamp S) (x : S) :
    coeff (Finsupp.single x 1) (lampPoly f) = Multiplicative.toAdd (f.toFun x) := by
  classical
  by_cases hx : x ∈ supp f
  · rw [lampPoly_eq_sum f (Finset.Subset.refl _), coeff_sum,
      Finset.sum_eq_single x]
    · rw [coeff_C_mul, coeff_X]
      simp
    · intro y _ hy
      rw [coeff_C_mul, coeff_X]
      have hne : ¬ (Finsupp.single y 1 = Finsupp.single x (1 : ℕ)) := by
        intro hcon
        exact hy (Finsupp.single_left_injective one_ne_zero hcon)
      rw [if_neg hne, mul_zero]
    · intro hcon
      exact absurd hx hcon
  · have hone : f.toFun x = 1 := by
      by_contra hcon
      exact hx (mem_supp.mpr hcon)
    rw [lampPoly, coeff_sum, Finset.sum_eq_zero, hone]
    · rfl
    · intro y hy
      rw [coeff_C_mul, coeff_X]
      have hne : ¬ (Finsupp.single y 1 = Finsupp.single x (1 : ℕ)) := by
        intro hcon
        exact hx (by
          rw [← Finsupp.single_left_injective one_ne_zero hcon]
          exact hy)
      rw [if_neg hne, mul_zero]

theorem lampPoly_injective : Function.Injective (lampPoly (S := S)) := by
  intro f g hfg
  refine Lamp.ext fun x => ?_
  have hcoeff := congrArg (coeff (Finsupp.single x 1)) hfg
  rw [coeff_lampPoly, coeff_lampPoly] at hcoeff
  exact Multiplicative.toAdd.injective hcoeff

/-! ## The unitriangular embedding -/

/-- The unitriangular matrix of a lamp configuration. -/
noncomputable def lampMatrix (f : TwoLamp S) :
    Matrix (Fin 2) (Fin 2) (MvPolynomial S (ZMod 2)) :=
  !![1, lampPoly f; 0, 1]

theorem lampMatrix_mul (f g : TwoLamp S) :
    lampMatrix (f * g) = lampMatrix f * lampMatrix g := by
  rw [lampMatrix, lampMatrix, lampMatrix, Matrix.mul_fin_two, lampPoly_mul]
  norm_num [add_comm]

theorem lampMatrix_one : lampMatrix (1 : TwoLamp S) = 1 := by
  have hzero : lampPoly (1 : TwoLamp S) = 0 := by
    rw [lampPoly]
    refine Finset.sum_eq_zero fun x hx => ?_
    exact absurd (mem_supp.mp hx) (by simp)
  rw [lampMatrix, hzero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The mod-two lamp group as a subgroup of two-by-two matrices over a
polynomial ring. -/
noncomputable def lampHom :
    TwoLamp S →* Matrix (Fin 2) (Fin 2) (MvPolynomial S (ZMod 2)) where
  toFun := lampMatrix
  map_one' := lampMatrix_one
  map_mul' := lampMatrix_mul

theorem lampHom_injective : Function.Injective (lampHom (S := S)) := by
  intro f g hfg
  refine lampPoly_injective ?_
  have := congrFun (congrFun (congrArg Matrix.of.symm hfg) 0) 1
  simpa [lampHom, lampMatrix] using
    congrArg (fun M : Matrix (Fin 2) (Fin 2) (MvPolynomial S (ZMod 2)) => M 0 1) hfg

/-- **Section 54.2, linearity clause.**  The mod-two lamp group embeds in
two-by-two matrices over a field. -/
theorem exists_faithful_linear_representation :
    ∃ (F : Type v) (_ : Field F) (ρ : TwoLamp S →* Matrix (Fin 2) (Fin 2) F),
      Function.Injective ρ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsDomain (MvPolynomial S (ZMod 2)) := inferInstance
  set φ : MvPolynomial S (ZMod 2) →+* FractionRing (MvPolynomial S (ZMod 2)) :=
    algebraMap _ _ with hφ
  have hφinj : Function.Injective φ :=
    IsFractionRing.injective (MvPolynomial S (ZMod 2))
      (FractionRing (MvPolynomial S (ZMod 2)))
  refine ⟨FractionRing (MvPolynomial S (ZMod 2)), inferInstance,
    { toFun := fun f => (lampMatrix f).map φ
      map_one' := by
        rw [lampMatrix_one]
        exact Matrix.map_one φ (map_zero φ) (map_one φ)
      map_mul' := fun f g => by
        rw [lampMatrix_mul]
        exact Matrix.map_mul }, ?_⟩
  intro f g hfg
  refine lampPoly_injective ?_
  have hentry := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) (FractionRing (MvPolynomial S (ZMod 2))) =>
      M 0 1) hfg
  have hpoly : lampMatrix f 0 1 = lampMatrix g 0 1 := hφinj hentry
  have h01 : ∀ h : TwoLamp S, lampMatrix h 0 1 = lampPoly h := by
    intro h
    rw [lampMatrix]
    simp
  rw [← h01 f, ← h01 g]
  exact hpoly

end LampLinear

end GroupApproximation
