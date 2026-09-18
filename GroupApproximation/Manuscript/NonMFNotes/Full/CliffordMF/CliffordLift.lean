import GroupApproximation.Monsters.CliffordAlgebraLamp

/-!
# Clifford lift of anticommuting involutions, and detection in the lamp group

This file serves `non_mf_group_notes.tex`, `\section{Necessity}`, paragraph
*Sharpness of the Kazhdan hypothesis* (tex ≈ 1163–1170).  It is the algebraic half of the
clause "So it is MF" for the realized Clifford quotient
`LiteralDyadicCalibration.DyadicRealizedQuotient`.

## What is proved here

* `anticommLift`: every family `e : X → A` of anticommuting involutions in a real algebra
  extends to an algebra map `CliffordAlgebra (euclidQ X) →ₐ[ℝ] A` with `lamp X x ↦ e x`
  (`anticommLift_lamp`).  This is the universal property of the Clifford algebra.
* `normalForm`: every element of the lamp group equals `(-1)^k * c_{x₁} ⋯ c_{xₙ}`.
* `lampGroup_detect`: when the site set is infinite, every nontrivial element `u` of the lamp
  group is either the central sign `z`, or satisfies `c_y u c_y = z u` for some lamp `c_y`.
  So any representation with `z ↦ z' ≠ 1` separates `u` from `1`.  This is the step that
  replaces the Schafhauser/TWW citation on the lamp part of the realized quotient.
-/

set_option linter.unusedSimpArgs false

namespace GroupApproximation.Full.NN10b

open GroupApproximation.CliffordAlgebraLamp

section Lift

variable {X : Type*} {A : Type*} [Ring A] [Algebra ℝ A]

/-- Polarized anticommutation: for anticommuting involutions `e`, the anticommutator of
the linear extensions of two vectors is twice their dot product. -/
theorem linearCombination_anticomm (e : X → A) (hsq : ∀ x, e x * e x = 1)
    (hanti : ∀ x y, x ≠ y → e x * e y = -(e y * e x)) (v w : X →₀ ℝ) :
    Finsupp.linearCombination ℝ e v * Finsupp.linearCombination ℝ e w +
        Finsupp.linearCombination ℝ e w * Finsupp.linearCombination ℝ e v =
      algebraMap ℝ A (2 * dotForm X v w) := by
  induction v using Finsupp.induction_linear with
  | zero => simp only [map_zero, zero_mul, mul_zero, add_zero, LinearMap.zero_apply]
  | add f g hf hg =>
    rw [map_add (Finsupp.linearCombination ℝ e) f g, add_mul, mul_add,
      map_add (dotForm X) f g, LinearMap.add_apply, mul_add, map_add (algebraMap ℝ A),
      ← hf, ← hg]
    abel
  | single a b =>
    induction w using Finsupp.induction_linear with
    | zero => simp only [map_zero, zero_mul, mul_zero, add_zero]
    | add f g hf hg =>
      rw [map_add (Finsupp.linearCombination ℝ e) f g, mul_add, add_mul,
        map_add (dotForm X (Finsupp.single a b)) f g, mul_add, map_add (algebraMap ℝ A),
        ← hf, ← hg]
      abel
    | single c d =>
      rw [Finsupp.linearCombination_single, Finsupp.linearCombination_single,
        smul_mul_smul_comm, smul_mul_smul_comm]
      by_cases hac : a = c
      · rw [hac, hsq, dotForm_single_same, mul_comm d b, Algebra.algebraMap_eq_smul_one,
          two_mul, add_smul]
      · rw [hanti a c hac, dotForm_single_of_ne X hac, mul_comm d b, smul_neg,
          neg_add_cancel, mul_zero, map_zero]

/-- The linear extension of anticommuting involutions squares to the quadratic form. -/
theorem linearCombination_mul_self (e : X → A) (hsq : ∀ x, e x * e x = 1)
    (hanti : ∀ x y, x ≠ y → e x * e y = -(e y * e x)) (v : X →₀ ℝ) :
    Finsupp.linearCombination ℝ e v * Finsupp.linearCombination ℝ e v =
      algebraMap ℝ A (euclidQ X v) := by
  show _ = algebraMap ℝ A (dotForm X v v)
  have h := linearCombination_anticomm e hsq hanti v v
  rw [two_mul, map_add] at h
  have hx : ∀ z : A, z = (2⁻¹ : ℝ) • (z + z) := by
    intro z
    rw [← two_smul ℝ z, smul_smul, inv_mul_cancel₀ (two_ne_zero : (2 : ℝ) ≠ 0), one_smul]
  rw [hx (Finsupp.linearCombination ℝ e v * Finsupp.linearCombination ℝ e v), h, ← hx]

/-- The universal Clifford lift of a family of anticommuting involutions. -/
noncomputable def anticommLift (e : X → A) (hsq : ∀ x, e x * e x = 1)
    (hanti : ∀ x y, x ≠ y → e x * e y = -(e y * e x)) :
    CliffordAlgebra (euclidQ X) →ₐ[ℝ] A :=
  CliffordAlgebra.lift (euclidQ X)
    ⟨Finsupp.linearCombination ℝ e, linearCombination_mul_self e hsq hanti⟩

/-- The Clifford lift sends the lamp at `x` to `e x`. -/
theorem anticommLift_lamp (e : X → A) (hsq : ∀ x, e x * e x = 1)
    (hanti : ∀ x y, x ≠ y → e x * e y = -(e y * e x)) (x : X) :
    anticommLift e hsq hanti (lamp X x) = e x := by
  unfold anticommLift lamp
  rw [CliffordAlgebra.lift_ι_apply, Finsupp.linearCombination_single, one_smul]

end Lift

section Word

variable (X : Type*)

/-- The lamp word `c_{x₁} ⋯ c_{xₙ}` of a list of sites. -/
noncomputable def lampWord (l : List X) : CliffordAlgebra (euclidQ X) :=
  l.foldr (fun x w => lamp X x * w) 1

theorem lampWord_nil : lampWord X [] = 1 := rfl

theorem lampWord_cons (x : X) (l : List X) :
    lampWord X (x :: l) = lamp X x * lampWord X l := rfl

theorem lampWord_append (s t : List X) :
    lampWord X (s ++ t) = lampWord X s * lampWord X t := by
  induction s with
  | nil => rw [List.nil_append, lampWord_nil, one_mul]
  | cons x s ih => rw [List.cons_append, lampWord_cons, lampWord_cons, ih, mul_assoc]

/-- Signs commute with everything. -/
theorem mul_neg_one_pow_comm (n : ℕ) (a : CliffordAlgebra (euclidQ X)) :
    a * (-1) ^ n = (-1) ^ n * a :=
  ((Commute.neg_one_left a).pow_left n).eq.symm

/-- **Normal form.** Every element of the lamp group is a signed lamp word. -/
theorem normalForm {u : (CliffordAlgebra (euclidQ X))ˣ} (hu : u ∈ lampGroup X) :
    ∃ (k : ℕ) (l : List X), (u : CliffordAlgebra (euclidQ X)) = (-1) ^ k * lampWord X l := by
  have hstep : ∀ s ∈ Set.range (lampUnit X) ∪ {zUnit X}, ∀ v : (CliffordAlgebra (euclidQ X))ˣ,
      (∃ (k : ℕ) (l : List X), (v : CliffordAlgebra (euclidQ X)) = (-1) ^ k * lampWord X l) →
      ∃ (k : ℕ) (l : List X),
        ((s * v : (CliffordAlgebra (euclidQ X))ˣ) : CliffordAlgebra (euclidQ X)) =
          (-1) ^ k * lampWord X l := by
    rintro s (⟨x, rfl⟩ | rfl) v ⟨k, l, h⟩
    · refine ⟨k, x :: l, ?_⟩
      rw [Units.val_mul, h, lampUnit_val, lampWord_cons, ← mul_assoc,
        mul_neg_one_pow_comm X k (lamp X x), mul_assoc]
    · refine ⟨k + 1, l, ?_⟩
      rw [Units.val_mul, h, zUnit_val, pow_succ' (-1 : CliffordAlgebra (euclidQ X)) k, mul_assoc]
  induction hu using Subgroup.closure_induction_left with
  | one => exact ⟨0, [], by rw [Units.val_one, pow_zero, lampWord_nil, one_mul]⟩
  | mul_left s hs v _ ih => exact hstep s hs v ih
  | inv_mul_cancel s hs v _ ih =>
    rcases hs with ⟨x, rfl⟩ | rfl
    · rw [lampUnit_inv]
      exact hstep _ (Or.inl ⟨x, rfl⟩) v ih
    · have hz : (zUnit X)⁻¹ = zUnit X := Units.ext rfl
      rw [hz]
      exact hstep _ (Or.inr rfl) v ih

/-- Moving a lamp through a lamp word costs one sign per letter, and one more per
occurrence of the same site. -/
theorem lamp_mul_lampWord [DecidableEq X] (y : X) (l : List X) :
    lamp X y * lampWord X l =
      (-1) ^ (l.length + l.count y) * (lampWord X l * lamp X y) := by
  induction l with
  | nil =>
    simp only [lampWord_nil, List.length_nil, List.count_nil, add_zero, pow_zero, one_mul,
      mul_one]
  | cons x l ih =>
    rw [lampWord_cons, ← mul_assoc]
    by_cases hxy : x = y
    · rw [hxy]
      have hW : lamp X y * lampWord X l * lamp X y =
          (-1) ^ (l.length + l.count y) * lampWord X l := by
        rw [ih, mul_assoc, mul_assoc, lamp_mul_self, mul_one]
      have hev : Even ((l.length + 1 + (l.count y + 1)) + (l.length + l.count y)) :=
        ⟨l.length + l.count y + 1, by omega⟩
      have key : ((-1 : CliffordAlgebra (euclidQ X)) ^ (l.length + 1 + (l.count y + 1))) *
          (-1) ^ (l.length + l.count y) = 1 := by
        rw [← pow_add]
        exact Even.neg_one_pow hev
      rw [lamp_mul_self, one_mul, List.length_cons, List.count_cons_self, hW, ← mul_assoc,
        key, one_mul]
    · calc lamp X y * lamp X x * lampWord X l
          = -(lamp X x * (lamp X y * lampWord X l)) := by
            rw [lamp_mul_lamp_of_ne X (Ne.symm hxy), neg_mul, mul_assoc]
        _ = -(lamp X x * ((-1) ^ (l.length + l.count y) * (lampWord X l * lamp X y))) := by
            rw [ih]
        _ = -((-1) ^ (l.length + l.count y) * (lamp X x * lampWord X l * lamp X y)) := by
            rw [← mul_assoc (lamp X x), mul_neg_one_pow_comm, mul_assoc, mul_assoc]
        _ = (-1) ^ ((x :: l).length + (x :: l).count y) *
              (lamp X x * lampWord X l * lamp X y) := by
            rw [List.length_cons, List.count_cons_of_ne hxy, ← neg_mul, ← neg_one_mul,
              ← pow_succ', add_right_comm]

/-- Conjugating a signed lamp word by a lamp. -/
theorem lamp_conj_signWord [DecidableEq X] (y : X) (k : ℕ) (l : List X) :
    lamp X y * ((-1) ^ k * lampWord X l) * lamp X y =
      (-1) ^ (l.length + l.count y) * ((-1) ^ k * lampWord X l) := by
  rw [← mul_assoc (lamp X y), mul_neg_one_pow_comm X k (lamp X y),
    mul_assoc ((-1 : CliffordAlgebra (euclidQ X)) ^ k), lamp_mul_lampWord X y l,
    mul_assoc, mul_assoc, mul_assoc, lamp_mul_self, mul_one, ← mul_assoc,
    mul_neg_one_pow_comm X (l.length + l.count y) ((-1 : CliffordAlgebra (euclidQ X)) ^ k),
    mul_assoc]

/-- A lamp word in which every site occurs an even number of times is a sign. -/
theorem lampWord_eq_neg_one_pow_of_even [DecidableEq X] :
    ∀ (n : ℕ) (l : List X), l.length ≤ n → (∀ y, l.count y % 2 = 0) →
      ∃ j : ℕ, lampWord X l = (-1) ^ j := by
  intro n
  induction n with
  | zero =>
    intro l hl _
    cases l with
    | nil => exact ⟨0, by rw [lampWord_nil, pow_zero]⟩
    | cons x l =>
      rw [List.length_cons] at hl
      exact absurd hl (by omega)
  | succ n ih =>
    intro l hl hc
    cases l with
    | nil => exact ⟨0, by rw [lampWord_nil, pow_zero]⟩
    | cons x l =>
      have h1 := hc x
      rw [List.count_cons_self] at h1
      have hx : x ∈ l := List.count_pos_iff.mp (by omega)
      obtain ⟨s, t, rfl⟩ := List.append_of_mem hx
      have hW : lampWord X (x :: (s ++ x :: t)) =
          (-1) ^ (s.length + s.count x) * lampWord X (s ++ t) := by
        rw [lampWord_cons, lampWord_append, lampWord_cons, lampWord_append, ← mul_assoc,
          lamp_mul_lampWord X x s, mul_assoc, mul_assoc, ← mul_assoc (lamp X x) (lamp X x),
          lamp_mul_self, one_mul]
      have hl' : (s ++ t).length ≤ n := by
        simp only [List.length_append, List.length_cons] at hl ⊢
        omega
      have hc' : ∀ y, (s ++ t).count y % 2 = 0 := by
        intro y
        have hy := hc y
        by_cases hyx : x = y
        · rw [← hyx] at hy ⊢
          rw [List.count_cons_self, List.count_append, List.count_cons_self] at hy
          rw [List.count_append]
          omega
        · rw [List.count_cons_of_ne hyx, List.count_append, List.count_cons_of_ne hyx] at hy
          rw [List.count_append]
          omega
      obtain ⟨j, hj⟩ := ih (s ++ t) hl' hc'
      exact ⟨s.length + s.count x + j, by rw [hW, hj, ← pow_add]⟩

/-- **Detection in the lamp group.** Over an infinite site set, a nontrivial element of the
lamp group is the central sign, or a lamp conjugates it to its product with the sign. -/
theorem lampGroup_detect [Infinite X] {u : (CliffordAlgebra (euclidQ X))ˣ}
    (hu : u ∈ lampGroup X) (hne : u ≠ 1) :
    u = zUnit X ∨ ∃ y, lampUnit X y * u * lampUnit X y = zUnit X * u := by
  classical
  obtain ⟨k, l, hkl⟩ := normalForm X hu
  by_cases hodd : ∃ y, (l.length + l.count y) % 2 = 1
  · obtain ⟨y, hy⟩ := hodd
    right
    refine ⟨y, Units.ext ?_⟩
    have ho : Odd (l.length + l.count y) := ⟨(l.length + l.count y) / 2, by omega⟩
    have hs : ((-1 : CliffordAlgebra (euclidQ X)) ^ (l.length + l.count y)) = -1 :=
      Odd.neg_one_pow ho
    rw [Units.val_mul, Units.val_mul, Units.val_mul, lampUnit_val, zUnit_val, hkl,
      lamp_conj_signWord X y k l, hs]
  · have heven : ∀ y, (l.length + l.count y) % 2 = 0 := by
      intro y
      by_contra h
      exact hodd ⟨y, by omega⟩
    obtain ⟨y₀, hy₀⟩ := Infinite.exists_notMem_finset l.toFinset
    have h0 : l.count y₀ = 0 :=
      List.count_eq_zero_of_not_mem (fun h => hy₀ (List.mem_toFinset.mpr h))
    have hlen : l.length % 2 = 0 := by
      have h2 := heven y₀
      omega
    have hc : ∀ y, l.count y % 2 = 0 := by
      intro y
      have h2 := heven y
      omega
    obtain ⟨j, hj⟩ := lampWord_eq_neg_one_pow_of_even X l.length l le_rfl hc
    by_cases hkj : (k + j) % 2 = 0
    · have he : Even (k + j) := ⟨(k + j) / 2, by omega⟩
      exfalso
      apply hne
      apply Units.ext
      rw [Units.val_one, hkl, hj, ← pow_add, Even.neg_one_pow he]
    · have ho : Odd (k + j) := ⟨(k + j) / 2, by omega⟩
      left
      apply Units.ext
      rw [zUnit_val, hkl, hj, ← pow_add]
      exact Odd.neg_one_pow ho

/-- **Detection in the lamp group**, subgroup form. -/
theorem lampGen_detect [Infinite X] (u : lampGroup X) (hne : u ≠ 1) :
    u = zGen X ∨ ∃ y, lampGen X y * u * lampGen X y = zGen X * u := by
  rcases lampGroup_detect X u.2 (fun h => hne (Subtype.ext h)) with h | ⟨y, hy⟩
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr ⟨y, Subtype.ext hy⟩

end Word

end GroupApproximation.Full.NN10b
