import GroupApproximation.CharClass.AcyclicModels
import GroupApproximation.CharClass.OddPGroupRing
import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# The standard periodic free resolution over a `ℤ/p`-group ring

`AcyclicModelsResolution.lean` builds the mod-2 resolution, in which the two
classically alternating differentials `1 − T` and `1 + T` *coincide*, so the
complex is built from one repeated map.  At odd `p` they do not coincide and the
resolution genuinely alternates:

```text
⋯ ⟶ Λ --(N)--> Λ --(s)--> Λ --(N)--> Λ --(s)--> Λ ⟶ F_p ⟶ 0 ,
     s = T − 1 ,   N = 1 + T + ⋯ + T^{p-1} .
```

This file records that pattern generically: for any commutative ring `Λ` and any
two elements `a b : Λ` with `a * b = 0` and `b * a = 0`, the complex with `Λ` in
every degree and differentials alternating between multiplication by `a` and by
`b` is a chain complex, termwise free of rank one.  The mod-2 file is the
instance `a = b = 1 + T`; it is **not** edited and **not** superseded, because
`Cartan*.lean` consumes it and the mod-2 LIX answer must keep building.

## Two design points, both learned from the mod-2 lanes

* The parity lives in **one** `if`, inside `altCoeff`, indexed by the *target*
  degree of the differential.  Indexing the resolution by "even degrees" and
  "odd degrees" as two families would make every degree an expression in the
  inputs, which is the failure mode `CartanMidFour`'s post-mortem is about.
* Both differentials are `LinearMap.mulLeft` of a scalar, so `d ∘ d = 0` is a
  statement about the product of two scalars and the whole parity argument is
  discharged once, in `altCoeff_mul_succ`.
-/

universe u

namespace GroupApproximation.CharClass

open CategoryTheory

section Alternating

variable {Λ : Type} [CommRing Λ] (a b : Λ)

/-- The scalar of the differential whose **target** is degree `i`: `a` in even
target degrees, `b` in odd ones. -/
noncomputable def altCoeff (i : ℕ) : Λ := if Even i then a else b

-- `altCoeff` needs no ring structure, so the section's `[CommRing Λ]` is
-- auto-included and unused; `-DwarningAsError=true` makes that a hard error.
omit [CommRing Λ] in
@[simp] theorem altCoeff_even {i : ℕ} (h : Even i) : altCoeff a b i = a := if_pos h

omit [CommRing Λ] in
@[simp] theorem altCoeff_odd {i : ℕ} (h : ¬ Even i) : altCoeff a b i = b := if_neg h

/-- Two consecutive scalars are `a * b` or `b * a`, in one order or the other. -/
theorem altCoeff_mul_succ (hab : a * b = 0) (hba : b * a = 0) (i : ℕ) :
    altCoeff a b i * altCoeff a b (i + 1) = 0 := by
  by_cases h : Even i
  · rw [altCoeff_even a b h, altCoeff_odd a b (by rw [Nat.even_add_one]; simpa using h)]
    exact hab
  · rw [altCoeff_odd a b h, altCoeff_even a b (by rw [Nat.even_add_one]; exact h)]
    exact hba

/-- The differential landing in degree `i`: left multiplication by `altCoeff a b i`. -/
noncomputable def altDiff (i : ℕ) : ModuleCat.of Λ Λ ⟶ ModuleCat.of Λ Λ :=
  ModuleCat.ofHom (LinearMap.mulLeft Λ (altCoeff a b i))

@[simp] theorem altDiff_apply (i : ℕ) (x : Λ) : (altDiff a b i) x = altCoeff a b i * x := by
  simp [altDiff]

/-- **The chain-complex condition.** -/
theorem altDiff_comp (hab : a * b = 0) (hba : b * a = 0) (i : ℕ) :
    altDiff a b (i + 1) ≫ altDiff a b i = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [altDiff, ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_zero,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.zero_apply]
  calc altCoeff a b i * (altCoeff a b (i + 1) * x)
      = altCoeff a b i * altCoeff a b (i + 1) * x := by ring
    _ = 0 * x := by rw [altCoeff_mul_succ a b hab hba i]
    _ = 0 := by ring

/-- **The alternating periodic resolution.**  `Λ` in every degree; the
differential into degree `i` is multiplication by `a` for `i` even and by `b` for
`i` odd. -/
noncomputable def altResolution (hab : a * b = 0) (hba : b * a = 0) :
    ChainComplex (ModuleCat.{0} Λ) ℕ :=
  ChainComplex.of (fun _ => ModuleCat.of Λ Λ) (fun i => altDiff a b i)
    (fun i => altDiff_comp a b hab hba i)

@[simp] theorem altResolution_X (hab : a * b = 0) (hba : b * a = 0) (k : ℕ) :
    (altResolution a b hab hba).X k = ModuleCat.of Λ Λ :=
  rfl

@[simp] theorem altResolution_d (hab : a * b = 0) (hba : b * a = 0) (k : ℕ) :
    (altResolution a b hab hba).d (k + 1) k = altDiff a b k := by
  unfold altResolution
  exact ChainComplex.of_d (fun _ : ℕ => ModuleCat.of Λ Λ) (fun i => altDiff a b i) k

/-- **Termwise freeness of rank one**: every degree is `Λ` itself, with the
one-point basis `{1}`. -/
noncomputable def altResolutionBasis (hab : a * b = 0) (hba : b * a = 0) (k : ℕ) :
    Module.Basis Unit Λ ((altResolution a b hab hba).X k) :=
  Module.Basis.singleton Unit Λ

end Alternating

/-- **The resolution at the mod-`p` group ring of `ℤ/p`.**  Multiplication by
`s = T − 1` into even degrees, by the norm `N` into odd ones. -/
noncomputable def Wodd (p : ℕ) : ChainComplex (ModuleCat.{0} (GroupRingZMod p)) ℕ :=
  altResolution (grS p) (grNorm p) (grS_mul_grNorm p) (grNorm_mul_grS p)

/-- The differential of `Wodd` into degree `0` is multiplication by `T − 1`. -/
theorem Wodd_d_zero (p : ℕ) :
    (Wodd p).d 1 0 = altDiff (grS p) (grNorm p) 0 :=
  altResolution_d _ _ _ _ 0

end GroupApproximation.CharClass
