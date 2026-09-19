import GroupApproximation.CharClass.ThomRestrictSquare
import GroupApproximation.CharClass.LIXThomAssembly

/-!
# `habs`: the coordinate image of the relative group is the Thom kernel

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`CharClass/LIXThomAssembly.lean` builds the degreewise Thom data from two named
inputs, `hinj0` and `habs`, and says of the second that it "is the one place the
geometry of the projectivisation enters".  This file discharges it.

The proof is one piece of algebra applied to one landed square.  The algebra:
if `Φ` is a linear equivalence, `range j = ker ρ`, and some **injective** `Ψ`
makes `Ψ ∘ T ∘ Φ = ρ`, then `range (Φ ∘ j) = ker T`.  The square is
`ThomChernDeg.absToSub_sum_lhTerm`, whose `Ψ` is the subspace's own Leray--Hirsch
combination at degree `2r`; that combination is injective because
`cc-cohom-api`'s `bijective_sum_lhTerm_of_graded` says it is bijective, and
`lhDomainCard r (2r) = r` holds at every `r`, including `r = 0`.

Exactness of the pair at the absolute group is packaged here as
`range_relToAbs_eq_ker_absToSub`, from the two halves that
`CharClass/RelativeLES.lean` already has.

## What remains after this file

`LIXThomAssembly.thomData_of_absToSub` still takes `hinj0`, injectivity of
`relToAbs` at degree `2r`.  That is a different input, discharged one degree down
by `cc-cohom-api`'s `absToSub_surjective_of_graded` through
`relToAbs_injective_of_absToSub_surjective`, and it is **not** what this file
proves.  Saying otherwise would be the undercount this lane has made before.

## Main declarations

* `range_relToAbs_eq_ker_absToSub` — exactness at `H^n(X)`, as an equality of submodules.
* `ThomChernDeg.range_comp_eq_ker_of_square` — the algebra.
* `ThomChernDeg.range_thomJm_eq_ker_restrictMap` — **`habs`**.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-! ## 1. Exactness at the absolute group, as submodules -/

/-- **Exactness at `H^n(X)`**, in the form a range/kernel statement takes.  The two
inclusions are `relToAbs_comp_absToSub` and `relLES_exact_abs`. -/
theorem range_relToAbs_eq_ker_absToSub (R : Type) [CommRing R] (X : TopCat.{0})
    (A : Set X) (n : ℕ) :
    LinearMap.range (relToAbs R X A n).hom = LinearMap.ker (absToSub R A n).hom := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    have hcomp := relToAbs_comp_absToSub R X A n
    have h := congrArg (fun f : relCohomology R X A n ⟶ _ => f.hom b) hcomp
    simpa using h
  · intro ha
    obtain ⟨b, hb⟩ := relLES_exact_abs R X A n a (LinearMap.mem_ker.mp ha)
    exact ⟨b, hb⟩

namespace ThomChernDeg

open LH

set_option linter.unusedSectionVars false

variable {X P : TopCat.{0}}

/-! ## 2. The algebra -/

/-- **From a commuting square with an injective bottom edge and one exactness, the
range of the coordinate map is a kernel.**

`Φ` reads a class in coordinates, `j` is the map whose range is the kernel of `ρ`,
`T` is the map in coordinates, and `Ψ` is the identification of the target of `ρ`
that makes the square commute.  Nothing here is topology. -/
theorem range_comp_eq_ker_of_square {A B C D E : Type}
    [AddCommGroup A] [Module (ZMod 2) A] [AddCommGroup B] [Module (ZMod 2) B]
    [AddCommGroup C] [Module (ZMod 2) C] [AddCommGroup D] [Module (ZMod 2) D]
    [AddCommGroup E] [Module (ZMod 2) E]
    (Φ : A ≃ₗ[ZMod 2] B) (j : C →ₗ[ZMod 2] A) (ρ : A →ₗ[ZMod 2] D)
    (T : B →ₗ[ZMod 2] E) (Ψ : E → D) (hΨ0 : Ψ 0 = 0) (hΨ : Function.Injective Ψ)
    (hex : LinearMap.range j = LinearMap.ker ρ)
    (hsq : ∀ x : A, Ψ (T (Φ x)) = ρ x) :
    LinearMap.range (Φ.toLinearMap.comp j) = LinearMap.ker T := by
  ext y
  constructor
  · rintro ⟨c, rfl⟩
    have hjc : ρ (j c) = 0 :=
      LinearMap.mem_ker.mp (hex ▸ LinearMap.mem_range_self j c)
    refine LinearMap.mem_ker.mpr (hΨ ?_)
    rw [hΨ0]
    exact (hsq (j c)).trans hjc
  · intro hy
    have hTy : T y = 0 := LinearMap.mem_ker.mp hy
    have hrho : ρ (Φ.symm y) = 0 := by
      rw [← hsq (Φ.symm y), Φ.apply_symm_apply, hTy, hΨ0]
    obtain ⟨c, hc⟩ : Φ.symm y ∈ LinearMap.range j := by
      rw [hex]; exact LinearMap.mem_ker.mpr hrho
    refine ⟨c, ?_⟩
    show Φ (j c) = y
    rw [hc, Φ.apply_symm_apply]

/-! ## 3. `habs` -/

/-- **The coordinate image of the relative group is the kernel of the restriction.**

This is the `habs` of `LIXThomAssembly.thomData_of_absToSub`, at
`coeff = LinearEquiv.refl` and `g i` multiplication by the `i`-th Chern
coefficient of the subspace's presentation.  The `hinj0` of that theorem is a
separate input and is not proved here. -/
theorem range_thomJm_eq_ker_restrictMap (Z : Set P)
    (π : P ⟶ X) (π' : TopCat.of Z ⟶ X) (hπ : sInclusion Z ≫ π = π')
    (ξ : Hmod2 P 2) (ξ' : Hmod2 (TopCat.of Z) 2) (hξ : pull (sInclusion Z) 2 ξ = ξ')
    {r : ℕ} (L : LerayHirschGraded π ξ (r + 1)) (L' : LerayHirschGraded π' ξ' r) :
    LinearMap.range (thomJm L Z)
      = LinearMap.ker (ThomDeg.restrictMap (R := ZMod 2)
          (M := fun i : Fin (r + 1) => Hmod2 X (2 * r - 2 * (i : ℕ)))
          (fun i => chernMul L' i)) := by
  have hΨinj : Function.Injective
      (fun b : (i : Fin r) → Hmod2 X (2 * r - 2 * (i : ℕ)) =>
        ∑ i : Fin r, lhTerm π' ξ' (2 * r) (i : ℕ) (b i)) :=
    (LHCast.bijective_sum_lhTerm_of_graded L' (2 * r) (lhDomainCard_two_mul r)).1
  refine range_comp_eq_ker_of_square (lhTopEquiv L).symm
    (relToAbs (ZMod 2) P Z (2 * r)).hom (absToSub (ZMod 2) Z (2 * r)).hom _
    (fun b => ∑ i : Fin r, lhTerm π' ξ' (2 * r) (i : ℕ) (b i)) ?_ hΨinj
    (range_relToAbs_eq_ker_absToSub (ZMod 2) P Z (2 * r)) ?_
  · exact Finset.sum_eq_zero (fun i _ => lhTerm_zero π' ξ' (2 * r) (i : ℕ))
  · intro x
    have hx : ∑ i : Fin (r + 1),
        lhTerm π ξ (2 * r) (i : ℕ) ((lhTopEquiv L).symm x i) = x :=
      (lhTopEquiv L).apply_symm_apply x
    have hsq := absToSub_sum_lhTerm Z π π' hπ ξ ξ' hξ L' ((lhTopEquiv L).symm x)
    rw [hx] at hsq
    exact hsq.symm

/-! Printed on every build. -/

#print axioms range_thomJm_eq_ker_restrictMap

end ThomChernDeg

end

end GroupApproximation.CharClass
