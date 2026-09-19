import GroupApproximation.Analysis.CStarStateGNS
import GroupApproximation.Analysis.CuntzPedersenCoronaObstruction
import Mathlib.Analysis.Normed.Module.WeakDual

/-!
# Producing a trace from finite tracial state constraints

This file replaces the Jordan-decomposition route to the rogue trace by a
compactness argument.  If every finite collection of self-commutators can be
annihilated by a state which takes a prescribed value on `h`, then
Banach--Alaoglu gives one state annihilating every self-commutator.  The
polarization identity then proves that this state is tracial.

The result is particularly suited to the projective-space construction.  At
one sufficiently large coordinate, the common-zero theorem may be applied to
both the lower-left corners of `z` and of `star z`; the corresponding vector
state annihilates each self-commutator in the chosen finite family and takes
value one on the obstruction.
-/

namespace GroupApproximation
namespace FiniteTraceCompactness

open CStarState CuntzPedersenCoronaObstruction
open scoped ComplexOrder

noncomputable section

set_option linter.unusedSectionVars false

universe u

variable {A : Type u} [CStarAlgebra A] [Nontrivial A]

/-- Weak-star closed constraints on a state: norm at most one, unitality, a
prescribed value one on `h`, and vanishing on the displayed finite family of
self-commutators. -/
def constraintSet (h : A) (S : Finset A) : Set (WeakDual ℂ A) :=
  {f | f.toStrongDual ∈ Metric.closedBall 0 1 ∧
    f 1 = 1 ∧ f h = 1 ∧
    ∀ z ∈ S, f (selfCommutator z) = 0}

theorem isClosed_constraintSet (h : A) (S : Finset A) :
    IsClosed (constraintSet h S) := by
  have hball : IsClosed
      {f : WeakDual ℂ A |
        f.toStrongDual ∈ Metric.closedBall (0 : StrongDual ℂ A) 1} :=
    WeakDual.isClosed_closedBall (0 : StrongDual ℂ A) 1
  have hone : IsClosed {f : WeakDual ℂ A | f 1 = (1 : ℂ)} :=
    isClosed_eq (WeakDual.eval_continuous (1 : A)) continuous_const
  have hh : IsClosed {f : WeakDual ℂ A | f h = (1 : ℂ)} :=
    isClosed_eq (WeakDual.eval_continuous h) continuous_const
  have hcomm : IsClosed
      {f : WeakDual ℂ A | ∀ z ∈ S, f (selfCommutator z) = 0} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun z ↦ isClosed_iInter fun _ ↦
      isClosed_eq (WeakDual.eval_continuous (selfCommutator z)) continuous_const
  rw [show constraintSet h S =
      {f : WeakDual ℂ A |
          f.toStrongDual ∈ Metric.closedBall (0 : StrongDual ℂ A) 1} ∩
        ({f : WeakDual ℂ A | f 1 = (1 : ℂ)} ∩
          ({f : WeakDual ℂ A | f h = (1 : ℂ)} ∩
            {f : WeakDual ℂ A |
              ∀ z ∈ S, f (selfCommutator z) = 0})) by
    ext f
    simp only [constraintSet, Set.mem_setOf_eq, Set.mem_inter_iff]]
  exact hball.inter (hone.inter (hh.inter hcomm))

theorem constraintSet_subset_closedBall (h : A) (S : Finset A) :
    constraintSet h S ⊆
      WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ A) 1 := by
  intro f hf
  exact hf.1

theorem isCompact_constraintSet (h : A) (S : Finset A) :
    IsCompact (constraintSet h S) :=
  (WeakDual.isCompact_closedBall (0 : StrongDual ℂ A) 1).of_isClosed_subset
    (isClosed_constraintSet h S) (constraintSet_subset_closedBall h S)

/-- A bundled state satisfying finite constraints gives a point of the
corresponding weak-star compact set. -/
theorem constraintSet_nonempty_of_state (h : A) (S : Finset A)
    (hex : ∃ φ : State A,
      φ.toCLM h = 1 ∧ ∀ z ∈ S, φ.toCLM (selfCommutator z) = 0) :
    (constraintSet h S).Nonempty := by
  obtain ⟨φ, hφh, hφS⟩ := hex
  refine ⟨StrongDual.toWeakDual φ.toCLM, ?_⟩
  refine ⟨?_, φ.map_one, hφh, hφS⟩
  simpa [Metric.mem_closedBall, dist_zero_right] using φ.norm_le

theorem directed_constraintSet (h : A) :
    Directed (· ⊇ ·) (constraintSet h) := by
  classical
  intro S T
  refine ⟨S ∪ T, ?_, ?_⟩
  · intro f hf
    exact ⟨hf.1, hf.2.1, hf.2.2.1,
      fun z hz ↦ hf.2.2.2 z (Finset.mem_union_left T hz)⟩
  · intro f hf
    exact ⟨hf.1, hf.2.1, hf.2.2.1,
      fun z hz ↦ hf.2.2.2 z (Finset.mem_union_right S hz)⟩

/-- Polarization: a complex-linear functional which annihilates every
additive self-commutator is tracial. -/
theorem map_mul_comm_of_selfCommutator_eq_zero
    (f : A →ₗ[ℂ] ℂ) (hf : ∀ z : A, f (selfCommutator z) = 0)
    (x y : A) : f (x * y) = f (y * x) := by
  let u : A := star x
  let v : A := y
  have hu := hf u
  have hv := hf v
  have hplus := hf (u + v)
  have himag := hf (u + Complex.I • v)
  simp only [selfCommutator, star_add, add_mul, mul_add, map_sub, map_add] at hu hv hplus
  simp only [selfCommutator, star_add, star_smul, Complex.star_def,
    Complex.conj_I, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    map_sub, map_add, map_smul, smul_eq_mul] at himag
  simp only [← mul_assoc, mul_neg, neg_mul, Complex.I_mul_I, neg_neg,
    one_mul] at himag
  have hsum :
      (f (star u * v) - f (v * star u)) +
        (f (star v * u) - f (u * star v)) = 0 := by
    linear_combination hplus - hu - hv
  have himag' :
      Complex.I * ((f (star u * v) - f (v * star u)) -
        (f (star v * u) - f (u * star v))) = 0 := by
    linear_combination himag - hu - hv
  have hdiff :
      (f (star u * v) - f (v * star u)) -
        (f (star v * u) - f (u * star v)) = 0 := by
    exact (mul_eq_zero.mp himag').resolve_left Complex.I_ne_zero
  have hz : f (star u * v) - f (v * star u) = 0 := by
    linear_combination (1 / 2 : ℂ) * (hsum + hdiff)
  exact sub_eq_zero.mp (by simpa only [u, v, star_star] using hz)

/-- **Finite tracial constraints compactness.**  Exact finite solvability by
states implies the existence of one tracial state satisfying all constraints.

This theorem is independent of Cuntz--Pedersen separation and of Jordan
decomposition. -/
theorem exists_tracialState_of_finite_state_constraints (h : A)
    (hfinite : ∀ S : Finset A, ∃ φ : State A,
      φ.toCLM h = 1 ∧ ∀ z ∈ S, φ.toCLM (selfCommutator z) = 0) :
    ∃ τ : TracialState A, τ h = 1 := by
  classical
  have hnonempty : ∀ S : Finset A, (constraintSet h S).Nonempty :=
    fun S ↦ constraintSet_nonempty_of_state h S (hfinite S)
  obtain ⟨f, hf⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (constraintSet h) (directed_constraintSet h) hnonempty
      (isCompact_constraintSet h) (isClosed_constraintSet h)
  have hfS : ∀ S : Finset A, f ∈ constraintSet h S :=
    Set.mem_iInter.mp hf
  have hnorm : ‖f.toStrongDual‖ ≤ 1 := by
    have hball := (hfS ∅).1
    simpa [Metric.mem_closedBall, dist_zero_right] using hball
  let φ : State A :=
    { toCLM := f.toStrongDual
      map_one := (hfS ∅).2.1
      norm_le := hnorm }
  have hcomm : ∀ z : A, φ.toCLM (selfCommutator z) = 0 := by
    intro z
    exact (hfS {z}).2.2.2 z (by simp)
  let τ : TracialState A :=
    { toLinearMap := φ.toCLM.toLinearMap
      map_one := φ.map_one
      map_star_mul_self_nonneg := fun x ↦
        Complex.nonneg_iff.mpr
          ⟨(φ.star_mul_self_nonneg x).1, (φ.star_mul_self_nonneg x).2.symm⟩
      map_mul_comm := fun x y ↦
        map_mul_comm_of_selfCommutator_eq_zero φ.toCLM hcomm x y }
  refine ⟨τ, ?_⟩
  exact (hfS ∅).2.2.1

/-! ## Simultaneously annihilating an ideal or other prescribed set -/

/-- Finite data for the compactness construction which also forces a
prescribed set to vanish.  The natural-number coordinate asks for the bound
`1 / (precision + 1)` on the displayed finite subset. -/
structure VanishingConstraintIndex (Z : Set A) where
  commutators : Finset A
  vanishing : Finset Z
  precision : ℕ

instance (Z : Set A) : Nonempty (VanishingConstraintIndex Z) :=
  ⟨⟨∅, ∅, 0⟩⟩

/-- Weak-star constraints combining exact finite traciality with increasingly
small values on a prescribed set. -/
def vanishingConstraintSet (h : A) (Z : Set A)
    (K : VanishingConstraintIndex Z) : Set (WeakDual ℂ A) :=
  {f | f.toStrongDual ∈ Metric.closedBall 0 1 ∧
    f 1 = 1 ∧ f h = 1 ∧
    (∀ z ∈ K.commutators, f (selfCommutator z) = 0) ∧
    ∀ a ∈ K.vanishing,
      ‖f a.1‖ ≤ 1 / (K.precision + 1 : ℝ)}

theorem isClosed_vanishingConstraintSet (h : A) (Z : Set A)
    (K : VanishingConstraintIndex Z) :
    IsClosed (vanishingConstraintSet h Z K) := by
  have hball : IsClosed
      {f : WeakDual ℂ A |
        f.toStrongDual ∈ Metric.closedBall (0 : StrongDual ℂ A) 1} :=
    WeakDual.isClosed_closedBall (0 : StrongDual ℂ A) 1
  have hone : IsClosed {f : WeakDual ℂ A | f 1 = (1 : ℂ)} :=
    isClosed_eq (WeakDual.eval_continuous (1 : A)) continuous_const
  have hh : IsClosed {f : WeakDual ℂ A | f h = (1 : ℂ)} :=
    isClosed_eq (WeakDual.eval_continuous h) continuous_const
  have hcomm : IsClosed
      {f : WeakDual ℂ A |
        ∀ z ∈ K.commutators, f (selfCommutator z) = 0} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun z ↦ isClosed_iInter fun _ ↦
      isClosed_eq (WeakDual.eval_continuous (selfCommutator z)) continuous_const
  have hv : IsClosed
      {f : WeakDual ℂ A | ∀ a ∈ K.vanishing,
        ‖f a.1‖ ≤ 1 / (K.precision + 1 : ℝ)} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun a ↦ isClosed_iInter fun _ ↦
      isClosed_Iic.preimage (WeakDual.eval_continuous a.1).norm
  rw [show vanishingConstraintSet h Z K =
      {f : WeakDual ℂ A |
          f.toStrongDual ∈ Metric.closedBall (0 : StrongDual ℂ A) 1} ∩
        ({f : WeakDual ℂ A | f 1 = (1 : ℂ)} ∩
          ({f : WeakDual ℂ A | f h = (1 : ℂ)} ∩
            ({f : WeakDual ℂ A |
                ∀ z ∈ K.commutators, f (selfCommutator z) = 0} ∩
              {f : WeakDual ℂ A | ∀ a ∈ K.vanishing,
                ‖f a.1‖ ≤ 1 / (K.precision + 1 : ℝ)}))) by
    ext f
    simp only [vanishingConstraintSet, Set.mem_setOf_eq, Set.mem_inter_iff]]
  exact hball.inter (hone.inter (hh.inter (hcomm.inter hv)))

theorem isCompact_vanishingConstraintSet (h : A) (Z : Set A)
    (K : VanishingConstraintIndex Z) :
    IsCompact (vanishingConstraintSet h Z K) :=
  (WeakDual.isCompact_closedBall (0 : StrongDual ℂ A) 1).of_isClosed_subset
    (isClosed_vanishingConstraintSet h Z K) (by
      intro f hf
      exact hf.1)

theorem directed_vanishingConstraintSet (h : A) (Z : Set A) :
    Directed (· ⊇ ·) (vanishingConstraintSet h Z) := by
  classical
  intro K L
  let M : VanishingConstraintIndex Z :=
    ⟨K.commutators ∪ L.commutators, K.vanishing ∪ L.vanishing,
      max K.precision L.precision⟩
  refine ⟨M, ?_, ?_⟩
  · intro f hf
    refine ⟨hf.1, hf.2.1, hf.2.2.1, ?_, ?_⟩
    · intro z hz
      exact hf.2.2.2.1 z (Finset.mem_union_left L.commutators hz)
    · intro a ha
      exact (hf.2.2.2.2 a (Finset.mem_union_left L.vanishing ha)).trans
        (one_div_le_one_div_of_le (by positivity) (by
          exact_mod_cast
            Nat.add_le_add_right (Nat.le_max_left K.precision L.precision) 1))
  · intro f hf
    refine ⟨hf.1, hf.2.1, hf.2.2.1, ?_, ?_⟩
    · intro z hz
      exact hf.2.2.2.1 z (Finset.mem_union_right K.commutators hz)
    · intro a ha
      exact (hf.2.2.2.2 a (Finset.mem_union_right K.vanishing ha)).trans
        (one_div_le_one_div_of_le (by positivity) (by
          exact_mod_cast
            Nat.add_le_add_right (Nat.le_max_right K.precision L.precision) 1))

/-- Finite solvability with arbitrarily small values on `Z` produces a
tracial state which is exactly zero on all of `Z`.  This is the form needed
to make coordinate vector states factor through a `c₀` corona. -/
theorem exists_tracialState_annihilating_of_finite_state_constraints
    (h : A) (Z : Set A)
    (hfinite : ∀ K : VanishingConstraintIndex Z, ∃ φ : State A,
      φ.toCLM h = 1 ∧
      (∀ z ∈ K.commutators, φ.toCLM (selfCommutator z) = 0) ∧
      ∀ a ∈ K.vanishing,
        ‖φ.toCLM a.1‖ ≤ 1 / (K.precision + 1 : ℝ)) :
    ∃ τ : TracialState A, τ h = 1 ∧ ∀ a ∈ Z, τ a = 0 := by
  classical
  have hnonempty : ∀ K : VanishingConstraintIndex Z,
      (vanishingConstraintSet h Z K).Nonempty := by
    intro K
    obtain ⟨φ, hφh, hφcomm, hφvan⟩ := hfinite K
    refine ⟨StrongDual.toWeakDual φ.toCLM, ?_⟩
    refine ⟨?_, φ.map_one, hφh, hφcomm, hφvan⟩
    simpa [Metric.mem_closedBall, dist_zero_right] using φ.norm_le
  obtain ⟨f, hf⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (vanishingConstraintSet h Z) (directed_vanishingConstraintSet h Z)
      hnonempty (isCompact_vanishingConstraintSet h Z)
      (isClosed_vanishingConstraintSet h Z)
  have hfK : ∀ K : VanishingConstraintIndex Z,
      f ∈ vanishingConstraintSet h Z K := Set.mem_iInter.mp hf
  let K₀ : VanishingConstraintIndex Z := ⟨∅, ∅, 0⟩
  have hnorm : ‖f.toStrongDual‖ ≤ 1 := by
    have hball := (hfK K₀).1
    simpa [Metric.mem_closedBall, dist_zero_right] using hball
  let φ : State A :=
    { toCLM := f.toStrongDual
      map_one := (hfK K₀).2.1
      norm_le := hnorm }
  have hcomm : ∀ z : A, φ.toCLM (selfCommutator z) = 0 := by
    intro z
    let K : VanishingConstraintIndex Z := ⟨{z}, ∅, 0⟩
    exact (hfK K).2.2.2.1 z (by simp [K])
  let τ : TracialState A :=
    { toLinearMap := φ.toCLM.toLinearMap
      map_one := φ.map_one
      map_star_mul_self_nonneg := fun x ↦
        Complex.nonneg_iff.mpr
          ⟨(φ.star_mul_self_nonneg x).1, (φ.star_mul_self_nonneg x).2.symm⟩
      map_mul_comm := fun x y ↦
        map_mul_comm_of_selfCommutator_eq_zero φ.toCLM hcomm x y }
  refine ⟨τ, (hfK K₀).2.2.1, ?_⟩
  intro a ha
  have hnormZero : ‖f a‖ = 0 := by
    apply le_antisymm
    · by_contra hne
      have hpos : 0 < ‖f a‖ := lt_of_not_ge hne
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
      let K : VanishingConstraintIndex Z := ⟨∅, {⟨a, ha⟩}, k⟩
      have hle := (hfK K).2.2.2.2 ⟨a, ha⟩ (by simp [K])
      exact (not_lt_of_ge hle) hk
    · exact norm_nonneg _
  exact norm_eq_zero.mp hnormZero

end

end FiniteTraceCompactness
end GroupApproximation
