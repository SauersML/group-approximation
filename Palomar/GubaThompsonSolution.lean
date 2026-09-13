/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Set.Finite.Basic
import Mathlib.GroupTheory.PresentedGroup
import GroupApproximation.ThompsonOre.X1Answer
import GroupApproximation.ThompsonOre.X1AnswerThompson

/-!
# Proof of the Guba Question 3.20 theorems

This file repeats the challenge's shared block byte for byte and proves the two theorems
`Palomar/comparator-guba-thompson.json` selects.

* `question_3_20` and `question_3_20_common_multiple` are the two halves of
  `GroupApproximation.ThompsonOre.one_sub_x1_solution`, carried to the challenge's `F`.  On its own
  copy of presentation (1.2) the development proves that `K[F]` has no zero divisors, V. Guba's
  Theorem 3.18 for `x₀`, and that `x₁` lies in a subgroup `H` with `e : H ≃* F` and `e x₁ = x₀`,
  whose conjugates are nested.
* `toOre` is the identity from the challenge's `F` to `GroupApproximation.ThompsonOre.ThompsonF`,
  which has the same generators and relators.  `exists_solution_of_mulEquiv` and
  `exists_common_multiple_of_mulEquiv` carry solutions back along a group isomorphism, through
  `MonoidAlgebra.domCongr`.
* `question_3_20_of` and `question_3_20_common_multiple_of` prove the same statements with those
  three facts as hypotheses, from `GroupApproximation.ThompsonOre.one_sub_solution_of_nested`.
* The model tests check that the statements are neither vacuous nor trivially true.  The abelian
  images of `F` in `ℤ` separate `x₀`, `x₁` and `1`.  Since `x₁` has infinite order, `1 - x₁` is not
  a left zero divisor, so every solution of the printed form has `v ≠ 0`.  With `1` in place of
  `x₁` the printed form is trivial and the Ore form fails.  The Ore form holds in `K[ℤ]`.

The prose of this module was written by Claude (Anthropic).
-/

namespace GubaThompson

noncomputable section

-- BEGIN SHARED BLOCK (kept byte-identical in `Palomar/GubaThompsonChallenge.lean` and `Palomar/GubaThompsonSolution.lean`)

/-- Guba's exponent notation `a^b = b⁻¹ab` (the survey, p. 3:6), in the free group on `x₀, x₁`. -/
def conjBy (a b : FreeGroup (Fin 2)) : FreeGroup (Fin 2) :=
  b⁻¹ * a * b

/-- The relators of presentation (1.2), `x₁^(x₀²) = x₁^(x₀x₁)` and `x₁^(x₀³) = x₁^(x₀²x₁)`, each
relation `u = v` written as `u * v⁻¹`, where `x₀ = FreeGroup.of 0` and `x₁ = FreeGroup.of 1`. -/
def thompsonRels : Set (FreeGroup (Fin 2)) :=
  {conjBy (FreeGroup.of 1) (FreeGroup.of 0 ^ 2) *
      (conjBy (FreeGroup.of 1) (FreeGroup.of 0 * FreeGroup.of 1))⁻¹,
    conjBy (FreeGroup.of 1) (FreeGroup.of 0 ^ 3) *
      (conjBy (FreeGroup.of 1) (FreeGroup.of 0 ^ 2 * FreeGroup.of 1))⁻¹}

/-- Thompson's group `F`, by presentation (1.2) of the survey. -/
abbrev ThompsonF : Type :=
  PresentedGroup thompsonRels

/-- The generator `x₀` of `F`. -/
def x0 : ThompsonF :=
  PresentedGroup.of 0

/-- The generator `x₁` of `F`. -/
def x1 : ThompsonF :=
  PresentedGroup.of 1

-- END SHARED BLOCK

/-! ## Transport along a group isomorphism -/

theorem domCongr_one_sub_of {K G G' : Type*} [CommRing K] [Group G] [Group G'] (φ : G ≃* G')
    (x : G) :
    MonoidAlgebra.domCongr K K φ (1 - MonoidAlgebra.of K G x) =
      1 - MonoidAlgebra.of K G' (φ x) := by
  rw [map_sub, map_one, MonoidAlgebra.of_apply, MonoidAlgebra.of_apply,
    MonoidAlgebra.domCongr_single]

/-- A solution of `(1 - φ x) u = φ(b) v` with `u ≠ 0 ∨ v ≠ 0` gives one of `(1 - x) u = b v`. -/
theorem exists_solution_of_mulEquiv {K G G' : Type*} [CommRing K] [Group G] [Group G']
    (φ : G ≃* G') (x : G) (b : MonoidAlgebra K G)
    (h : ∃ u v : MonoidAlgebra K G', (u ≠ 0 ∨ v ≠ 0) ∧
      (1 - MonoidAlgebra.of K G' (φ x)) * u = MonoidAlgebra.domCongr K K φ b * v) :
    ∃ u v : MonoidAlgebra K G, (u ≠ 0 ∨ v ≠ 0) ∧ (1 - MonoidAlgebra.of K G x) * u = b * v := by
  obtain ⟨u, v, huv, heq⟩ := h
  have hne : ∀ w : MonoidAlgebra K G', w ≠ 0 → (MonoidAlgebra.domCongr K K φ).symm w ≠ 0 := by
    intro w hw h0
    apply hw
    rw [← AlgEquiv.apply_symm_apply (MonoidAlgebra.domCongr K K φ) w, h0, map_zero]
  refine ⟨(MonoidAlgebra.domCongr K K φ).symm u, (MonoidAlgebra.domCongr K K φ).symm v,
    huv.imp (hne u) (hne v), ?_⟩
  apply (MonoidAlgebra.domCongr K K φ).injective
  rw [map_mul, map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply,
    domCongr_one_sub_of, heq]

/-- A solution of `(1 - φ x) u = φ(b) v` with `φ(b) v ≠ 0` gives one of `(1 - x) u = b v` with
`b v ≠ 0`. -/
theorem exists_common_multiple_of_mulEquiv {K G G' : Type*} [CommRing K] [Group G] [Group G']
    (φ : G ≃* G') (x : G) (b : MonoidAlgebra K G)
    (h : ∃ u v : MonoidAlgebra K G', MonoidAlgebra.domCongr K K φ b * v ≠ 0 ∧
      (1 - MonoidAlgebra.of K G' (φ x)) * u = MonoidAlgebra.domCongr K K φ b * v) :
    ∃ u v : MonoidAlgebra K G, b * v ≠ 0 ∧ (1 - MonoidAlgebra.of K G x) * u = b * v := by
  obtain ⟨u, v, hbv, heq⟩ := h
  refine ⟨(MonoidAlgebra.domCongr K K φ).symm u, (MonoidAlgebra.domCongr K K φ).symm v,
    fun h0 => hbv ?_, ?_⟩
  · rw [← AlgEquiv.apply_symm_apply (MonoidAlgebra.domCongr K K φ) v,
      ← map_mul (MonoidAlgebra.domCongr K K φ), h0, map_zero]
  · apply (MonoidAlgebra.domCongr K K φ).injective
    rw [map_mul, map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply,
      domCongr_one_sub_of, heq]

/-! ## The two theorems from three facts about `F` taken as hypotheses -/

/-- **Question 3.20 from three facts about `F`**: if `K[F]` has no zero divisors, Theorem 3.18
holds for `x₀`, and `x₁` lies in a subgroup `H` with `e : H ≃* F`, `e x₁ = x₀`, whose conjugates
are nested, then for every `b ∈ K[F]` the equation `(1 - x₁) u = b v` has a solution
`(u, v) ≠ (0, 0)`. -/
theorem question_3_20_of (K : Type*) [Field K] [NoZeroDivisors (MonoidAlgebra K ThompsonF)]
    (h318 : ∀ b : MonoidAlgebra K ThompsonF, b ≠ 0 →
      ∃ v, b * v ≠ 0 ∧ ∃ u, b * v = (1 - MonoidAlgebra.of K ThompsonF x0) * u)
    (H : Subgroup ThompsonF) (hx1 : x1 ∈ H) (e : H ≃* ThompsonF) (he : e ⟨x1, hx1⟩ = x0)
    (hchain : ∀ c : ThompsonF, (∀ f ∈ H, c * f * c⁻¹ ∈ H) ∨ (∀ f ∈ H, c⁻¹ * f * c ∈ H))
    (b : MonoidAlgebra K ThompsonF) :
    ∃ u v : MonoidAlgebra K ThompsonF,
      (u ≠ 0 ∨ v ≠ 0) ∧ (1 - MonoidAlgebra.of K ThompsonF x1) * u = b * v :=
  (GroupApproximation.ThompsonOre.one_sub_solution_of_nested x0 x1 H hx1 e he h318 hchain b).1

/-- **The Ore form from three facts about `F`**: under the hypotheses of `question_3_20_of`, for
every non-zero `b ∈ K[F]` the right ideals `(1 - x₁) K[F]` and `b K[F]` meet in a non-zero
element. -/
theorem question_3_20_common_multiple_of (K : Type*) [Field K]
    [NoZeroDivisors (MonoidAlgebra K ThompsonF)]
    (h318 : ∀ b : MonoidAlgebra K ThompsonF, b ≠ 0 →
      ∃ v, b * v ≠ 0 ∧ ∃ u, b * v = (1 - MonoidAlgebra.of K ThompsonF x0) * u)
    (H : Subgroup ThompsonF) (hx1 : x1 ∈ H) (e : H ≃* ThompsonF) (he : e ⟨x1, hx1⟩ = x0)
    (hchain : ∀ c : ThompsonF, (∀ f ∈ H, c * f * c⁻¹ ∈ H) ∨ (∀ f ∈ H, c⁻¹ * f * c ∈ H))
    (b : MonoidAlgebra K ThompsonF) (hb : b ≠ 0) :
    ∃ u v : MonoidAlgebra K ThompsonF,
      b * v ≠ 0 ∧ (1 - MonoidAlgebra.of K ThompsonF x1) * u = b * v :=
  (GroupApproximation.ThompsonOre.one_sub_solution_of_nested x0 x1 H hx1 e he h318 hchain b).2 hb

/-! ## The two theorems -/

/-- The challenge's `F` is `GroupApproximation.ThompsonOre.ThompsonF`: both are presentation (1.2)
with the same generators and relators, so the identity is an isomorphism between them. -/
def toOre : ThompsonF ≃* GroupApproximation.ThompsonOre.ThompsonF :=
  MulEquiv.refl _

theorem toOre_x1 : toOre x1 = GroupApproximation.ThompsonOre.x1 :=
  rfl

/-- **Question 3.20 has a positive answer**: for every field `K` and every `b ∈ K[F]`, the
equation `(1 - x₁) u = b v` has a solution `(u, v) ≠ (0, 0)`. -/
theorem question_3_20 (K : Type*) [Field K] (b : MonoidAlgebra K ThompsonF) :
    ∃ u v : MonoidAlgebra K ThompsonF,
      (u ≠ 0 ∨ v ≠ 0) ∧ (1 - MonoidAlgebra.of K ThompsonF x1) * u = b * v := by
  refine exists_solution_of_mulEquiv toOre x1 b ?_
  rw [toOre_x1]
  exact (GroupApproximation.ThompsonOre.one_sub_x1_solution
    (MonoidAlgebra.domCongr K K toOre b)).1

/-- **The Ore form**: for every non-zero `b ∈ K[F]` the right ideals `(1 - x₁) K[F]` and
`b K[F]` meet in a non-zero element. -/
theorem question_3_20_common_multiple (K : Type*) [Field K]
    (b : MonoidAlgebra K ThompsonF) (hb : b ≠ 0) :
    ∃ u v : MonoidAlgebra K ThompsonF,
      b * v ≠ 0 ∧ (1 - MonoidAlgebra.of K ThompsonF x1) * u = b * v := by
  refine exists_common_multiple_of_mulEquiv toOre x1 b ?_
  rw [toOre_x1]
  have hb' : MonoidAlgebra.domCongr K K toOre b ≠ 0 := fun h0 =>
    hb ((MonoidAlgebra.domCongr K K toOre).injective
      (h0.trans (map_zero (MonoidAlgebra.domCongr K K toOre)).symm))
  exact (GroupApproximation.ThompsonOre.one_sub_x1_solution
    (MonoidAlgebra.domCongr K K toOre b)).2 hb'

/-! ## Model tests of the statements -/

namespace ModelTests

theorem lift_conjBy_of_comm {G : Type*} [CommGroup G] (f : Fin 2 → G) (a b : FreeGroup (Fin 2)) :
    FreeGroup.lift f (conjBy a b) = FreeGroup.lift f a := by
  rw [conjBy, map_mul, map_mul, map_inv, mul_comm (FreeGroup.lift f b)⁻¹, inv_mul_cancel_right]

theorem lift_thompsonRels_of_comm {G : Type*} [CommGroup G] (f : Fin 2 → G) :
    ∀ r ∈ thompsonRels, FreeGroup.lift f r = 1 := by
  intro r hr
  simp only [thompsonRels, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl <;>
    rw [map_mul, map_inv, lift_conjBy_of_comm, lift_conjBy_of_comm, mul_inv_cancel]

/-- The abelian image of `F` in `ℤ` with `x₀ ↦ a` and `x₁ ↦ b`. -/
def toZ (a b : ℤ) : ThompsonF →* Multiplicative ℤ :=
  PresentedGroup.toGroup
    (lift_thompsonRels_of_comm ![Multiplicative.ofAdd a, Multiplicative.ofAdd b])

theorem toZ_x0 (a b : ℤ) : toZ a b x0 = Multiplicative.ofAdd a := by
  simp [toZ, x0]

theorem toZ_x1 (a b : ℤ) : toZ a b x1 = Multiplicative.ofAdd b := by
  simp [toZ, x1]

theorem x0_ne_one : x0 ≠ 1 := by
  intro h
  have h2 : toZ 1 0 x0 = toZ 1 0 1 := by rw [h]
  simp [toZ_x0] at h2

theorem x1_ne_one : x1 ≠ 1 := by
  intro h
  have h2 : toZ 0 1 x1 = toZ 0 1 1 := by rw [h]
  simp [toZ_x1] at h2

theorem x0_ne_x1 : x0 ≠ x1 := by
  intro h
  have h2 : toZ 1 0 x0 = toZ 1 0 x1 := by rw [h]
  simp [toZ_x0, toZ_x1] at h2

/-- `x₁` has infinite order in `F`. -/
theorem pow_x1_injective : Function.Injective fun n : ℕ => x1 ^ n := by
  intro m n h
  have h1 : x1 ^ m = x1 ^ n := h
  have h2 : Multiplicative.toAdd (toZ 0 1 (x1 ^ m)) =
      Multiplicative.toAdd (toZ 0 1 (x1 ^ n)) := by
    rw [h1]
  simpa [toZ_x1] using h2

/-- In the group ring of any group, `1 - h` is not a left zero divisor when `h` has infinite
order. -/
theorem eq_zero_of_one_sub_of_mul_eq_zero {K G : Type*} [Ring K] [Group G] {h : G}
    (hh : Function.Injective fun n : ℕ => h ^ n) {u : MonoidAlgebra K G}
    (hu : (1 - MonoidAlgebra.of K G h) * u = 0) : u = 0 := by
  have h1 : u = MonoidAlgebra.of K G h * u := by
    rwa [sub_mul, one_mul, sub_eq_zero] at hu
  have hfix : ∀ g : G, u.coeff (h * g) = u.coeff g := by
    intro g
    calc u.coeff (h * g) = (MonoidAlgebra.of K G h * u).coeff (h * g) := by rw [← h1]
      _ = u.coeff g := by
        rw [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single_mul_apply, one_mul,
          inv_mul_cancel_left]
  have hpow : ∀ (n : ℕ) (g : G), u.coeff (h ^ n * g) = u.coeff g := by
    intro n
    induction n with
    | zero => intro g; rw [pow_zero, one_mul]
    | succ n ih => intro g; rw [pow_succ', mul_assoc, hfix, ih]
  by_contra hne
  have hc : u.coeff ≠ 0 := fun h0 =>
    hne (MonoidAlgebra.coeff_inj.mp (h0.trans MonoidAlgebra.coeff_zero.symm))
  obtain ⟨g, hg⟩ := Finsupp.support_nonempty_iff.mpr hc
  have hmem : ∀ n : ℕ, h ^ n * g ∈ (u.coeff.support : Set G) := by
    intro n
    simp only [Finset.mem_coe, Finsupp.mem_support_iff, hpow]
    exact Finsupp.mem_support_iff.mp hg
  exact Set.infinite_of_injective_forall_mem (f := fun n : ℕ => h ^ n * g)
    (fun m n hmn => hh (mul_right_cancel hmn)) hmem (Finset.finite_toSet _)

theorem eq_zero_of_one_sub_x1_mul_eq_zero {K : Type*} [Field K] {u : MonoidAlgebra K ThompsonF}
    (hu : (1 - MonoidAlgebra.of K ThompsonF x1) * u = 0) : u = 0 :=
  eq_zero_of_one_sub_of_mul_eq_zero pow_x1_injective hu

/-- Every non-zero solution of the printed equation has `v ≠ 0`. -/
theorem solution_v_ne_zero {K : Type*} [Field K] {b u v : MonoidAlgebra K ThompsonF}
    (huv0 : u ≠ 0 ∨ v ≠ 0) (huv : (1 - MonoidAlgebra.of K ThompsonF x1) * u = b * v) :
    v ≠ 0 := by
  rintro rfl
  rw [mul_zero] at huv
  exact huv0.elim (fun hu => hu (eq_zero_of_one_sub_x1_mul_eq_zero huv)) (fun hv => hv rfl)

/-- Negative model for the printed form: with `x₁` replaced by `1` it holds trivially, by
`(u, v) = (1, 0)`.  `solution_v_ne_zero` rules such solutions out for `x₁`. -/
theorem question_form_trivial_for_one (K : Type*) [Field K] (b : MonoidAlgebra K ThompsonF) :
    ∃ u v : MonoidAlgebra K ThompsonF,
      (u ≠ 0 ∨ v ≠ 0) ∧ (1 - MonoidAlgebra.of K ThompsonF 1) * u = b * v :=
  ⟨1, 0, Or.inl one_ne_zero, by rw [map_one, sub_self, zero_mul, mul_zero]⟩

/-- Negative model for the Ore form: with `x₁` replaced by `1` it fails at `b = 1`. -/
theorem common_multiple_fails_for_one (K : Type*) [Field K] :
    ¬ ∀ b : MonoidAlgebra K ThompsonF, b ≠ 0 → ∃ u v : MonoidAlgebra K ThompsonF,
      b * v ≠ 0 ∧ (1 - MonoidAlgebra.of K ThompsonF 1) * u = b * v := by
  intro h
  obtain ⟨u, v, hv, huv⟩ := h 1 one_ne_zero
  rw [map_one, sub_self, zero_mul] at huv
  exact hv huv.symm

theorem pow_ofAdd_one_injective :
    Function.Injective fun n : ℕ => (Multiplicative.ofAdd (1 : ℤ)) ^ n := by
  intro m n h
  have h1 : (Multiplicative.ofAdd (1 : ℤ)) ^ m = (Multiplicative.ofAdd (1 : ℤ)) ^ n := h
  have h2 : Multiplicative.toAdd ((Multiplicative.ofAdd (1 : ℤ)) ^ m) =
      Multiplicative.toAdd ((Multiplicative.ofAdd (1 : ℤ)) ^ n) := by
    rw [h1]
  simpa using h2

/-- Positive model for the Ore form: in the group ring of `ℤ` it holds for the generator `t`,
with `u = b` and `v = 1 - t`. -/
theorem common_multiple_commutative_model (K : Type*) [Field K]
    (b : MonoidAlgebra K (Multiplicative ℤ)) (hb : b ≠ 0) :
    ∃ u v : MonoidAlgebra K (Multiplicative ℤ), b * v ≠ 0 ∧
      (1 - MonoidAlgebra.of K (Multiplicative ℤ) (Multiplicative.ofAdd 1)) * u = b * v := by
  refine ⟨b, 1 - MonoidAlgebra.of K (Multiplicative ℤ) (Multiplicative.ofAdd 1),
    fun h0 => hb ?_, mul_comm _ _⟩
  rw [mul_comm] at h0
  exact eq_zero_of_one_sub_of_mul_eq_zero pow_ofAdd_one_injective h0

end ModelTests

end

end GubaThompson
