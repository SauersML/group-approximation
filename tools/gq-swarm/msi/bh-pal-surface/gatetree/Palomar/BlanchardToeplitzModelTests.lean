/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Palomar.BlanchardToeplitzChallenge

/-!
# Model tests for the Blanchard Question 5.4 challenge

The definitions of `Palomar/BlanchardToeplitzChallenge.lean` on small inputs, each predicate and
set both positively and negatively where a negative instance is available:

* `cubeDist`: `d(x, x) = 0`.
* `tensorCoord`: `ζ ⊗ ω` vanishes at the empty word and is `ζ_i ω_w` at `i :: w`.
* `IsSectionAdjoint`: the identity is its own adjoint; `0` is not an adjoint of the identity on
  the full section space.
* `IsProperlyInfiniteSet`: every set of operators on the zero module is properly infinite; the
  empty set is not, and `{1}` on the full section space is not.
* `continuousSections`, `etaMultiples`, `ddModule`: each contains `0` and none contains the
  constant section `x ↦ e_none`.
* `fockGenerators`: `0` is a degree-zero generator; the vacuum is no generator of positive degree.
* `toeplitzAlgebra`: it contains `1`.

The prose of this module was written by Claude (Anthropic).
-/

namespace BlanchardToeplitz

namespace ModelTests

noncomputable section

open scoped ENNReal InnerProductSpace ComplexConjugate

theorem ennreal_two_pos : (0 : ℝ≥0∞) < 2 := by norm_num

/-- The origin of `B_∞`. -/
def origin : HilbertCube := ⟨0, by rw [norm_zero]; exact zero_le_one⟩

/-- The point `e_0` of `B_∞`. -/
def pointOne : HilbertCube :=
  ⟨lp.single 2 0 (1 : ℂ),
    (lp.norm_single (E := fun _ : ℕ => ℂ) ennreal_two_pos 0 (1 : ℂ)).trans_le norm_one.le⟩

/-- The constant section `x ↦ e_none` of the fibre `ℓ²(ℕ) ⊕ ℂ`. -/
def constNone : Sections K :=
  ⟨fun _ => (lp.single 2 none (1 : ℂ) : K), memℓp_infty ⟨1, by
    rintro _ ⟨x, rfl⟩
    exact (lp.norm_single (E := fun _ : Option ℕ => ℂ) ennreal_two_pos none (1 : ℂ)).trans_le
      norm_one.le⟩⟩

/-- The constant section `x ↦ e_[]` of the Fock space, the vacuum. -/
def vacuum : Sections Fock :=
  ⟨fun _ => (lp.single 2 [] (1 : ℂ) : Fock), memℓp_infty ⟨1, by
    rintro _ ⟨x, rfl⟩
    exact (lp.norm_single (E := fun _ : List (Option ℕ) => ℂ) ennreal_two_pos [] (1 : ℂ)).trans_le
      norm_one.le⟩⟩

theorem constNone_apply_none (x : HilbertCube) : (constNone x : Option ℕ → ℂ) none = 1 := by
  show (lp.single 2 none (1 : ℂ) : K) none = 1
  exact lp.single_apply_self _ _ _

theorem inner_vacuum_self (x : HilbertCube) : ⟪vacuum x, vacuum x⟫_ℂ = 1 := by
  show ⟪(lp.single 2 [] (1 : ℂ) : Fock), (lp.single 2 [] (1 : ℂ) : Fock)⟫_ℂ = 1
  rw [lp.inner_single_left, lp.single_apply_self, RCLike.inner_apply', map_one, one_mul]

/-! ### `cubeDist` and `tensorCoord` -/

theorem cubeDist_self (x : HilbertCube) : cubeDist x x = 0 := by
  simp only [cubeDist, sub_self, norm_zero, mul_zero, tsum_zero]

theorem tensorCoord_nil (ζ : Option ℕ → ℂ) (ω : List (Option ℕ) → ℂ) :
    tensorCoord ζ ω [] = 0 := rfl

theorem tensorCoord_cons (ζ : Option ℕ → ℂ) (ω : List (Option ℕ) → ℂ) (i : Option ℕ)
    (w : List (Option ℕ)) : tensorCoord ζ ω (i :: w) = ζ i * ω w := rfl

/-! ### `IsSectionAdjoint` -/

theorem isSectionAdjoint_one_one (M : Submodule ℂ (Sections Fock)) :
    IsSectionAdjoint (1 : Module.End ℂ M) 1 :=
  fun _ _ _ => rfl

theorem not_isSectionAdjoint_one_zero :
    ¬ IsSectionAdjoint (1 : Module.End ℂ (⊤ : Submodule ℂ (Sections Fock))) 0 := by
  intro h
  have h1 := h ⟨vacuum, Submodule.mem_top⟩ ⟨vacuum, Submodule.mem_top⟩ origin
  change ⟪vacuum origin, vacuum origin⟫_ℂ =
    ⟪vacuum origin, ((0 : Sections Fock) origin : Fock)⟫_ℂ at h1
  simp only [lp.coeFn_zero, Pi.zero_apply, inner_zero_right] at h1
  rw [inner_vacuum_self] at h1
  exact one_ne_zero h1

/-! ### `IsProperlyInfiniteSet` -/

theorem isProperlyInfiniteSet_univ_bot :
    IsProperlyInfiniteSet (Set.univ : Set (Module.End ℂ (⊥ : Submodule ℂ (Sections Fock)))) := by
  have hall : ∀ S T : Module.End ℂ (⊥ : Submodule ℂ (Sections Fock)), S = T :=
    fun _ _ => LinearMap.ext fun _ => Subsingleton.elim _ _
  have hadj : ∀ S T : Module.End ℂ (⊥ : Submodule ℂ (Sections Fock)), IsSectionAdjoint S T := by
    intro S T ξ η x
    rw [Subsingleton.elim (S ξ) ξ, Subsingleton.elim (T η) η]
  exact ⟨1, Set.mem_univ _, 1, Set.mem_univ _, 1, 1, hadj _ _, hadj _ _, hall _ _, hall _ _,
    hall _ _⟩

theorem not_isProperlyInfiniteSet_empty (M : Submodule ℂ (Sections Fock)) :
    ¬ IsProperlyInfiniteSet (∅ : Set (Module.End ℂ M)) :=
  fun ⟨s, hs, _⟩ => Set.notMem_empty s hs

theorem not_isProperlyInfiniteSet_one :
    ¬ IsProperlyInfiniteSet ({1} : Set (Module.End ℂ (⊤ : Submodule ℂ (Sections Fock)))) := by
  rintro ⟨s₁, hs₁, s₂, hs₂, t₁, t₂, -, -, h₁, h₂, h⟩
  rw [Set.mem_singleton_iff] at hs₁ hs₂
  subst hs₁ hs₂
  rw [mul_one] at h₁ h₂
  subst h₁ h₂
  have hv := LinearMap.congr_fun h ⟨vacuum, Submodule.mem_top⟩
  have h1 := congrArg (fun ω : (⊤ : Submodule ℂ (Sections Fock)) =>
    (((ω : Sections Fock) origin : Fock) : List (Option ℕ) → ℂ) []) hv
  change (lp.single 2 [] (1 : ℂ) : Fock) [] =
    (((0 : Sections Fock) origin : Fock) : List (Option ℕ) → ℂ) [] at h1
  exact one_ne_zero (by simpa only [lp.single_apply_self, lp.coeFn_zero, Pi.zero_apply] using h1)

/-! ### `continuousSections`, `etaMultiples`, `ddModule` -/

theorem zero_mem_continuousSections : (0 : Sections K) ∈ continuousSections := by
  refine ⟨?_, fun x => ?_⟩
  · simp only [lp.coeFn_zero, Pi.zero_apply]
    exact continuous_const
  · simp only [lp.coeFn_zero, Pi.zero_apply]

theorem constNone_not_mem_continuousSections : constNone ∉ continuousSections :=
  fun h => one_ne_zero ((constNone_apply_none origin).symm.trans (h.2 origin))

theorem zero_mem_etaMultiples : (0 : Sections K) ∈ etaMultiples :=
  ⟨⟨fun _ => 0, continuous_const⟩, fun x i => by
    simp only [lp.coeFn_zero, Pi.zero_apply, ContinuousMap.coe_mk, zero_mul]⟩

theorem etaCoord_pointOne_none : etaCoord pointOne none = 0 := by
  show (Real.sqrt (1 - ‖(lp.single 2 0 (1 : ℂ) : L2)‖ ^ 2) : ℂ) = 0
  rw [lp.norm_single ennreal_two_pos, norm_one, one_pow, sub_self, Real.sqrt_zero,
    Complex.ofReal_zero]

theorem constNone_not_mem_etaMultiples : constNone ∉ etaMultiples := by
  rintro ⟨f, hf⟩
  have h := hf pointOne none
  rw [etaCoord_pointOne_none, mul_zero, constNone_apply_none] at h
  exact one_ne_zero h

theorem zero_mem_ddModule : (0 : Sections K) ∈ ddModule :=
  ⟨0, Submodule.zero_mem _, fun x i => by
    simp only [lp.coeFn_zero, Pi.zero_apply, mul_zero, tsum_zero, zero_mul, sub_zero]⟩

theorem etaCoord_origin_some (p : ℕ) : etaCoord origin (some p) = 0 := by
  show ((0 : L2) : ℕ → ℂ) p = 0
  simp only [lp.coeFn_zero, Pi.zero_apply]

theorem etaCoord_origin_none : etaCoord origin none = 1 := by
  show (Real.sqrt (1 - ‖(0 : L2)‖ ^ 2) : ℂ) = 1
  rw [norm_zero, zero_pow two_ne_zero, sub_zero, Real.sqrt_one, Complex.ofReal_one]

theorem constNone_not_mem_ddModule : constNone ∉ ddModule := by
  rintro ⟨ξ, -, hξ⟩
  have hsum : (∑' j, conj (etaCoord origin j) * (ξ origin : Option ℕ → ℂ) j) =
      (ξ origin : Option ℕ → ℂ) none := by
    rw [tsum_eq_single none, etaCoord_origin_none, map_one, one_mul]
    rintro (_ | p) hp
    · exact absurd rfl hp
    · rw [etaCoord_origin_some, map_zero, zero_mul]
  have h := hξ origin none
  rw [hsum, etaCoord_origin_none, mul_one, sub_self, constNone_apply_none] at h
  exact one_ne_zero h

/-! ### `fockGenerators` and `toeplitzAlgebra` -/

theorem zero_mem_fockGenerators_zero (E : Set (Sections K)) :
    (0 : Sections Fock) ∈ fockGenerators E 0 :=
  ⟨⟨fun _ => 0, continuous_const⟩, fun x w => by
    simp only [lp.coeFn_zero, Pi.zero_apply, ContinuousMap.coe_mk, ite_self]⟩

theorem vacuum_not_mem_fockGenerators_succ (E : Set (Sections K)) (m : ℕ) :
    vacuum ∉ fockGenerators E (m + 1) := by
  rintro ⟨ζ, -, ω, -, h⟩
  have h1 := h origin []
  change (lp.single 2 [] (1 : ℂ) : Fock) [] = 0 at h1
  rw [lp.single_apply_self] at h1
  exact one_ne_zero h1

theorem one_mem_toeplitzAlgebra (E : Set (Sections K)) : 1 ∈ toeplitzAlgebra E :=
  Set.mem_sInter.2 fun _ h𝒯 => h𝒯.1

end

end ModelTests

end BlanchardToeplitz
