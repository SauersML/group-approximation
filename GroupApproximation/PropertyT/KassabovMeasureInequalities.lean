import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Abstract measure inequalities in Kassabov's relative-property-`(T)` argument

This module isolates the measure arithmetic used after a spectral measure has
been constructed.  It does not construct a spectral measure, mention a
representation, or assume relative property `(T)`.

The source argument only uses a nonnegative real-valued finitely additive
measure on the full power set.  `RealFiniteAdditiveMeasure` records exactly
that data.  The principal result is the disjoint-union transport estimate: if
`A` is partitioned into `s` pieces, the images of those pieces are disjoint
inside `B`, and inverse transport changes mass at scale `epsilon`, then

`sqrt (mu A) <= sqrt (mu B) + sqrt |s| * epsilon`.

The factor `sqrt |s|`, rather than `|s|`, is the Cauchy--Schwarz gain in
Kassabov's Lemma 2.5.  Every declaration below is unconditional.
-/

namespace GroupApproximation

universe u v

namespace KassabovMeasureInequalities

open Set
open scoped BigOperators

/-- A finite, real-valued, finitely additive measure defined on every subset.
The adjective `finite` refers to its real-valued mass: no set can have infinite
mass.  Normalization is deliberately absent. -/
structure RealFiniteAdditiveMeasure (Omega : Type u) where
  mass : Set Omega → ℝ
  empty : mass ∅ = 0
  nonnegative : ∀ A, 0 ≤ mass A
  union_of_disjoint : ∀ A B, Disjoint A B →
    mass (A ∪ B) = mass A + mass B

namespace RealFiniteAdditiveMeasure

variable {Omega : Type u} (mu : RealFiniteAdditiveMeasure Omega)

instance : CoeFun (RealFiniteAdditiveMeasure Omega)
    (fun _ ↦ Set Omega → ℝ) :=
  ⟨RealFiniteAdditiveMeasure.mass⟩

@[simp] theorem empty_apply : mu (∅ : Set Omega) = 0 := mu.empty

/-- Finite additivity and nonnegativity imply monotonicity. -/
theorem mono {A B : Set Omega} (hAB : A ⊆ B) : mu A ≤ mu B := by
  have hdis : Disjoint A (B \ A) := Set.disjoint_sdiff_right
  have hunion : A ∪ (B \ A) = B := by
    rw [Set.union_sdiff_self]
    exact Set.union_eq_right.mpr hAB
  rw [← hunion, mu.union_of_disjoint A (B \ A) hdis]
  exact le_add_of_nonneg_right (mu.nonnegative _)

/-- The mass of a finite pairwise-disjoint union is the sum of the masses. -/
theorem mass_biUnion_finset {I : Type v} (s : Finset I)
    (A : I → Set Omega)
    (hdis : Set.Pairwise (↑s) fun i j ↦ Disjoint (A i) (A j)) :
    mu (⋃ i ∈ s, A i) = ∑ i ∈ s, mu (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hAi : Disjoint (A i) (⋃ j ∈ s, A j) := by
        rw [Set.disjoint_iUnion_right]
        intro j
        rw [Set.disjoint_iUnion_right]
        intro hj
        exact hdis (Finset.mem_insert_self i s)
          (Finset.mem_insert_of_mem hj) (fun hij ↦ hi (hij ▸ hj))
      have hs : Set.Pairwise (↑s) fun j k ↦ Disjoint (A j) (A k) := by
        intro j hj k hk hjk
        exact hdis (Finset.mem_insert_of_mem hj)
          (Finset.mem_insert_of_mem hk) hjk
      have hunion : (⋃ j ∈ insert i s, A j) = A i ∪ ⋃ j ∈ s, A j := by
        simp
      have hadd := mu.union_of_disjoint (A i) (⋃ j ∈ s, A j) hAi
      rw [hunion, hadd, ih hs, Finset.sum_insert hi]

end RealFiniteAdditiveMeasure

/-! ## The numerical square-root estimates -/

/-- A one-sided quadratic mass estimate becomes a one-sided square-root
estimate. -/
theorem sqrt_le_sqrt_add_of_le_add_two_mul_sqrt
    {a b epsilon : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hepsilon : 0 ≤ epsilon)
    (h : a ≤ b + 2 * epsilon * Real.sqrt b + epsilon ^ 2) :
    Real.sqrt a ≤ Real.sqrt b + epsilon := by
  have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have hsb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  have hrhs : 0 ≤ Real.sqrt b + epsilon :=
    add_nonneg (Real.sqrt_nonneg b) hepsilon
  apply (sq_le_sq₀ (Real.sqrt_nonneg a) hrhs).mp
  rw [hsa]
  nlinarith

/-- The numerical core of the disjoint-union argument.  Summing the
individual transport inequalities and applying Cauchy--Schwarz to the square
roots produces `sqrt(card s) * epsilon`, not `card s * epsilon`. -/
theorem sqrt_sum_le_sqrt_bound_add_sqrt_card_mul
    {I : Type v} (s : Finset I) (a b : I → ℝ) (B epsilon : ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i)
    (hB : ∑ i ∈ s, b i ≤ B) (hB0 : 0 ≤ B) (hepsilon : 0 ≤ epsilon)
    (htransport : ∀ i ∈ s,
      a i ≤ b i + 2 * epsilon * Real.sqrt (b i) + epsilon ^ 2) :
    Real.sqrt (∑ i ∈ s, a i) ≤
      Real.sqrt B + Real.sqrt (s.card : ℝ) * epsilon := by
  classical
  let r : ℝ := ∑ i ∈ s, Real.sqrt (b i)
  have hr0 : 0 ≤ r :=
    Finset.sum_nonneg fun i hi ↦ Real.sqrt_nonneg (b i)
  have hcauchy : r ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, b i := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
      (fun _ ↦ (1 : ℝ)) (fun i ↦ Real.sqrt (b i))
    have hsquares :
        ∑ i ∈ s, Real.sqrt (b i) ^ 2 = ∑ i ∈ s, b i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Real.sq_sqrt (hb i hi)
    simpa [r, hsquares] using hcs
  have hcard0 : 0 ≤ (s.card : ℝ) := Nat.cast_nonneg _
  have hcauchyB : r ^ 2 ≤ (s.card : ℝ) * B :=
    hcauchy.trans (mul_le_mul_of_nonneg_left hB hcard0)
  have hproductSq :
      (Real.sqrt (s.card : ℝ) * Real.sqrt B) ^ 2 =
        (s.card : ℝ) * B := by
    rw [mul_pow, Real.sq_sqrt hcard0, Real.sq_sqrt hB0]
  have hrBound : r ≤ Real.sqrt (s.card : ℝ) * Real.sqrt B := by
    have hprod0 : 0 ≤ Real.sqrt (s.card : ℝ) * Real.sqrt B :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    apply (sq_le_sq₀ hr0 hprod0).mp
    rwa [hproductSq]
  have hsumTransport :
      ∑ i ∈ s, a i ≤
        ∑ i ∈ s, (b i + 2 * epsilon * Real.sqrt (b i) + epsilon ^ 2) :=
    Finset.sum_le_sum htransport
  have hsumUpper :
      ∑ i ∈ s, a i ≤
        (Real.sqrt B + Real.sqrt (s.card : ℝ) * epsilon) ^ 2 := by
    have hcross : 2 * epsilon * r ≤
        2 * epsilon * (Real.sqrt (s.card : ℝ) * Real.sqrt B) :=
      mul_le_mul_of_nonneg_left hrBound (mul_nonneg (by norm_num) hepsilon)
    calc
      ∑ i ∈ s, a i ≤
          ∑ i ∈ s,
            (b i + 2 * epsilon * Real.sqrt (b i) + epsilon ^ 2) :=
        hsumTransport
      _ = (∑ i ∈ s, b i) + 2 * epsilon * r +
          (s.card : ℝ) * epsilon ^ 2 := by
        simp [r, Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ B + 2 * epsilon *
          (Real.sqrt (s.card : ℝ) * Real.sqrt B) +
            (s.card : ℝ) * epsilon ^ 2 := by
        linarith
      _ = (Real.sqrt B + Real.sqrt (s.card : ℝ) * epsilon) ^ 2 := by
        nlinarith [Real.sq_sqrt hB0, Real.sq_sqrt hcard0]
  have hsumA0 : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg ha
  have hrhs0 : 0 ≤ Real.sqrt B + Real.sqrt (s.card : ℝ) * epsilon :=
    add_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) hepsilon)
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) hrhs0).mp
  rwa [Real.sq_sqrt hsumA0]

/-! ## Quasi-invariance and disjoint-union transport -/

variable {Omega : Type u}

/-- Kassabov's setwise quadratic quasi-invariance estimate at scale
`epsilon`. -/
def QuasiInvariantAtScale (mu : RealFiniteAdditiveMeasure Omega)
    (epsilon : ℝ) (g : Equiv.Perm Omega) : Prop :=
  ∀ A : Set Omega,
    |mu (g '' A) - mu A| ≤
      2 * epsilon * Real.sqrt (mu A) + epsilon ^ 2

/-- If the quadratic setwise bound holds in both directions, the square roots
of the two masses differ by at most `epsilon`.  This is the abstract numerical
content of the second formulation of Kassabov's Lemma 2.4. -/
theorem abs_sqrt_mass_image_sub_le
    (mu : RealFiniteAdditiveMeasure Omega) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (g : Equiv.Perm Omega)
    (hg : QuasiInvariantAtScale mu epsilon g)
    (hginv : QuasiInvariantAtScale mu epsilon g.symm)
    (A : Set Omega) :
    |Real.sqrt (mu (g '' A)) - Real.sqrt (mu A)| ≤ epsilon := by
  have hforwardAbs := hg A
  have hforward :
      mu (g '' A) ≤ mu A + 2 * epsilon * Real.sqrt (mu A) + epsilon ^ 2 := by
    linarith [le_abs_self (mu (g '' A) - mu A)]
  have hbackSet : g.symm '' (g '' A) = A := by
    ext x
    simp
  have hbackAbs := hginv (g '' A)
  rw [hbackSet] at hbackAbs
  have hback :
      mu A ≤ mu (g '' A) +
        2 * epsilon * Real.sqrt (mu (g '' A)) + epsilon ^ 2 := by
    linarith [le_abs_self (mu A - mu (g '' A))]
  have hle := sqrt_le_sqrt_add_of_le_add_two_mul_sqrt
    (mu.nonnegative _) (mu.nonnegative _) hepsilon hforward
  have hge := sqrt_le_sqrt_add_of_le_add_two_mul_sqrt
    (mu.nonnegative _) (mu.nonnegative _) hepsilon hback
  rw [abs_le]
  constructor <;> linarith

/-- **Disjoint-union transport.**  The source pieces are pairwise disjoint,
their transported images are pairwise disjoint inside `B`, and inverse
transport satisfies the quadratic quasi-invariance estimate.  Then transport
costs only `sqrt(card s) * epsilon` at square-root mass scale. -/
theorem sqrt_mass_biUnion_le_of_disjoint_transport
    {I : Type v} (mu : RealFiniteAdditiveMeasure Omega)
    (s : Finset I) (A : I → Set Omega) (B : Set Omega)
    (g : I → Equiv.Perm Omega) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hA_disjoint : Set.Pairwise (↑s) fun i j ↦ Disjoint (A i) (A j))
    (himage_disjoint : Set.Pairwise (↑s) fun i j ↦
      Disjoint (g i '' A i) (g j '' A j))
    (himage_subset : (⋃ i ∈ s, g i '' A i) ⊆ B)
    (hquasi : ∀ i ∈ s, QuasiInvariantAtScale mu epsilon (g i).symm) :
    Real.sqrt (mu (⋃ i ∈ s, A i)) ≤
      Real.sqrt (mu B) + Real.sqrt (s.card : ℝ) * epsilon := by
  classical
  have hmassA := mu.mass_biUnion_finset s A hA_disjoint
  have hmassImage :=
    mu.mass_biUnion_finset s (fun i ↦ g i '' A i) himage_disjoint
  have himageMass : ∑ i ∈ s, mu (g i '' A i) ≤ mu B := by
    rw [← hmassImage]
    exact mu.mono himage_subset
  have htransport : ∀ i ∈ s,
      mu (A i) ≤ mu (g i '' A i) +
        2 * epsilon * Real.sqrt (mu (g i '' A i)) + epsilon ^ 2 := by
    intro i hi
    have hbackSet : (g i).symm '' (g i '' A i) = A i := by
      ext x
      simp
    have hq := hquasi i hi (g i '' A i)
    rw [hbackSet] at hq
    linarith [le_abs_self (mu (A i) - mu (g i '' A i))]
  rw [hmassA]
  exact sqrt_sum_le_sqrt_bound_add_sqrt_card_mul s
    (fun i ↦ mu (A i)) (fun i ↦ mu (g i '' A i))
    (mu B) epsilon
    (fun i _ ↦ mu.nonnegative (A i))
    (fun i _ ↦ mu.nonnegative (g i '' A i))
    himageMass (mu.nonnegative B) hepsilon htransport

end KassabovMeasureInequalities

end GroupApproximation
