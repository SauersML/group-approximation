import GroupApproximation.Sofic.ExteriorMFProfile
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Sharp weight-theoretic lower bound for norm-to-trace conversion

This file develops the new lower-bound mechanism for the fermionic
norm-to-trace paper.  The representation-theoretic input is classical: a
finite-dimensional unitary representation restricted to a diagonal torus
splits into integral weights.  The paper-specific point is the sharp
quantitative synthesis:

* a coordinate sign flip sees precisely the weights with odd coordinate;
* odd integral weight contributes at least one unit of infinitesimal square;
* a Rademacher choice combines all coordinate contributions without loss.

Together these give the constant `1/2`, replacing the earlier exponential
path estimate and its constant `1/π`.
-/

namespace GroupApproximation

open scoped BigOperators RealInnerProductSpace Matrix.Norms.L2Operator

noncomputable section

/-! ## Lossless Rademacher selection in a real Hilbert space -/

/-- For finitely many vectors in a real Hilbert space, some choice of signs
has squared norm at least the sum of their squared norms.  This is the
deterministic form of the elementary Rademacher second-moment identity. -/
theorem exists_sign_sum_norm_sq_ge
    {ι E : Type*} [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Finset ι) (v : ι → E) :
    ∃ ε : ι → ℝ,
      (∀ i ∈ s, ε i = 1 ∨ ε i = -1) ∧
      (∑ i ∈ s, ‖v i‖ ^ 2) ≤ ‖∑ i ∈ s, ε i • v i‖ ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨fun _ ↦ 1, ?_, ?_⟩
      · simp
      · simp
  | @insert a s ha ih =>
      obtain ⟨ε, hε, hnorm⟩ := ih
      let y : E := ∑ i ∈ s, ε i • v i
      by_cases hinner : 0 ≤ inner ℝ (v a) y
      · let ε' : ι → ℝ := Function.update ε a 1
        refine ⟨ε', ?_, ?_⟩
        · intro i hi
          rw [Finset.mem_insert] at hi
          rcases hi with rfl | hi
          · left
            simp [ε']
          · have hia : i ≠ a := fun h ↦ ha (h ▸ hi)
            simpa [ε', hia] using hε i hi
        · have hsum : (∑ i ∈ insert a s, ε' i • v i) = v a + y := by
            rw [Finset.sum_insert ha]
            have hfirst : ε' a • v a = v a := by
              simp [ε']
            rw [hfirst]
            congr 1
            change (∑ i ∈ s, ε' i • v i) = ∑ i ∈ s, ε i • v i
            apply Finset.sum_congr rfl
            intro i hi
            have hia : i ≠ a := fun h ↦ ha (h ▸ hi)
            simp [ε', hia]
          rw [Finset.sum_insert ha, hsum, norm_add_sq_real]
          nlinarith
      · let ε' : ι → ℝ := Function.update ε a (-1)
        refine ⟨ε', ?_, ?_⟩
        · intro i hi
          rw [Finset.mem_insert] at hi
          rcases hi with rfl | hi
          · right
            simp [ε']
          · have hia : i ≠ a := fun h ↦ ha (h ▸ hi)
            simpa [ε', hia] using hε i hi
        · have hsum : (∑ i ∈ insert a s, ε' i • v i) = -v a + y := by
            rw [Finset.sum_insert ha]
            have hfirst : ε' a • v a = -v a := by
              simp [ε']
            rw [hfirst]
            congr 1
            change (∑ i ∈ s, ε' i • v i) = ∑ i ∈ s, ε i • v i
            apply Finset.sum_congr rfl
            intro i hi
            have hia : i ≠ a := fun h ↦ ha (h ▸ hi)
            simp [ε', hia]
          have hinner' : inner ℝ (v a) y < 0 := lt_of_not_ge hinner
          rw [Finset.sum_insert ha, hsum, norm_add_sq_real]
          simp only [norm_neg, inner_neg_left]
          nlinarith

/-- Full finite-type form of `exists_sign_sum_norm_sq_ge`. -/
theorem exists_rademacher_norm_sq_ge
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) :
    ∃ ε : ι → ℝ,
      (∀ i, ε i = 1 ∨ ε i = -1) ∧
      (∑ i, ‖v i‖ ^ 2) ≤ ‖∑ i, ε i • v i‖ ^ 2 := by
  classical
  simpa using exists_sign_sum_norm_sq_ge (Finset.univ : Finset ι) v

/-! ## Integral weights and the sharp `1/2` constant -/

/-- An odd integer has real square at least one. -/
theorem one_le_sq_intCast_of_odd {m : ℤ} (hm : Odd m) :
    (1 : ℝ) ≤ (m : ℝ) ^ 2 := by
  have hm0 : m ≠ 0 := by
    intro h
    subst m
    norm_num at hm
  have habs : (1 : ℤ) ≤ |m| := Int.one_le_abs hm0
  have habsR : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast habs
  nlinarith [sq_abs (m : ℝ)]

/-- Number of weight vectors whose `j`th coordinate is odd. -/
def oddWeightCount {Ω ι : Type*} [Fintype Ω]
    (weight : Ω → ι → ℤ) (j : ι) : ℕ :=
  Finset.card (Finset.univ.filter fun ω ↦ Odd (weight ω j))

/-- Every odd coordinate contributes at least one to the sum of coordinate
squares. -/
theorem oddWeightCount_le_sum_sq
    {Ω ι : Type*} [Fintype Ω]
    (weight : Ω → ι → ℤ) (j : ι) :
    (oddWeightCount weight j : ℝ) ≤
      ∑ ω : Ω, (weight ω j : ℝ) ^ 2 := by
  classical
  unfold oddWeightCount
  rw [show (Finset.card (Finset.univ.filter fun ω ↦ Odd (weight ω j)) : ℝ) =
      ∑ _ω ∈ Finset.univ.filter fun ω ↦ Odd (weight ω j), (1 : ℝ) by simp]
  calc
    (∑ _ω ∈ Finset.univ.filter fun ω ↦ Odd (weight ω j), (1 : ℝ))
        ≤ ∑ ω ∈ Finset.univ.filter fun ω ↦ Odd (weight ω j),
            (weight ω j : ℝ) ^ 2 := by
              apply Finset.sum_le_sum
              intro ω hω
              exact one_le_sq_intCast_of_odd (Finset.mem_filter.mp hω).2
    _ ≤ ∑ ω : Ω, (weight ω j : ℝ) ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro ω _ _
          positivity

/-- **Sharp torus-weight lower bound.**  If every coordinate sign flip has
squared normalized-HS displacement `Δ²`, so that the odd-weight fraction is
`Δ²/4`, then one diagonal operator-norm-one direction has infinitesimal
normalized-HS square at least `d Δ²/4`.

The statement is kept in denominator-free finite-sum form.  Dividing by the
positive output dimension gives the normalized theorem immediately. -/
theorem exists_weight_direction_sum_sq_ge_odd_counts
    {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (weight : Ω → ι → ℤ) :
    ∃ ε : ι → ℝ,
      (∀ i, ε i = 1 ∨ ε i = -1) ∧
      (∑ j : ι, (oddWeightCount weight j : ℝ)) ≤
        ∑ ω : Ω, (∑ j : ι, ε j * (weight ω j : ℝ)) ^ 2 := by
  classical
  let v : ι → EuclideanSpace ℝ Ω := fun j ↦
    WithLp.toLp 2 fun ω ↦ (weight ω j : ℝ)
  obtain ⟨ε, hε, hnorm⟩ := exists_rademacher_norm_sq_ge v
  refine ⟨ε, hε, ?_⟩
  calc
    (∑ j : ι, (oddWeightCount weight j : ℝ))
        ≤ ∑ j : ι, ∑ ω : Ω, (weight ω j : ℝ) ^ 2 := by
          exact Finset.sum_le_sum fun j _ ↦ oddWeightCount_le_sum_sq weight j
    _ = ∑ j : ι, ‖v j‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro j _
          rw [EuclideanSpace.real_norm_sq_eq]
    _ ≤ ‖∑ j : ι, ε j • v j‖ ^ 2 := hnorm
    _ = ∑ ω : Ω, (∑ j : ι, ε j * (weight ω j : ℝ)) ^ 2 := by
          rw [EuclideanSpace.real_norm_sq_eq]
          apply Finset.sum_congr rfl
          intro ω _
          congr 1
          simp [v]

/-! ## Normalized profiles and exact fermionic constant -/

/-- Finite weight data for the restriction of a unitary representation to a
coordinate torus.  Classical torus representation theory supplies such a
profile for every finite-dimensional continuous unitary representation of
`U(d)`. -/
structure TorusWeightProfile (ι : Type*) [Fintype ι] where
  weights : FiniteModel
  nonempty : 0 < Fintype.card weights
  weight : weights → ι → ℤ

namespace TorusWeightProfile

variable {ι : Type*} [Fintype ι]

/-- Squared normalized-HS displacement of the `j`th coordinate sign flip,
read from its torus weights. -/
noncomputable def signFlipDistSq (P : TorusWeightProfile ι) (j : ι) : ℝ :=
  4 * oddWeightCount P.weight j / Fintype.card P.weights

/-- Squared normalized infinitesimal HS norm in a diagonal direction `x`. -/
noncomputable def infinitesimalDistSq
    (P : TorusWeightProfile ι) (x : ι → ℝ) : ℝ :=
  (∑ ω : P.weights, (∑ j : ι, x j * (P.weight ω j : ℝ)) ^ 2) /
    Fintype.card P.weights

/-- Every coordinate sign is visible by at least squared distance `Δ²`. -/
def DetectsCoordinateSigns (P : TorusWeightProfile ι) (Δsq : ℝ) : Prop :=
  ∀ j, Δsq ≤ P.signFlipDistSq j

/-- Squared local operator-to-normalized-HS cost bounded by `L²` on all
diagonal sign directions, each of operator norm one. -/
def HasDiagonalLipschitzSq (P : TorusWeightProfile ι) (Lsq : ℝ) : Prop :=
  ∀ ε : ι → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) →
    P.infinitesimalDistSq ε ≤ Lsq

/-- The sharp weight theorem in normalized form. -/
theorem exists_sign_infinitesimalDistSq_ge_average_signFlipDistSq
    (P : TorusWeightProfile ι) :
    ∃ ε : ι → ℝ,
      (∀ j, ε j = 1 ∨ ε j = -1) ∧
      (∑ j : ι, P.signFlipDistSq j) / 4 ≤
        P.infinitesimalDistSq ε := by
  obtain ⟨ε, hε, hraw⟩ :=
    exists_weight_direction_sum_sq_ge_odd_counts P.weight
  refine ⟨ε, hε, ?_⟩
  unfold signFlipDistSq infinitesimalDistSq
  have hcard : (0 : ℝ) < Fintype.card P.weights := by
    exact_mod_cast P.nonempty
  calc
    (∑ j : ι, 4 * (oddWeightCount P.weight j : ℝ) /
          Fintype.card P.weights) / 4 =
        (∑ j : ι, (oddWeightCount P.weight j : ℝ)) /
          Fintype.card P.weights := by
            calc
              (∑ j : ι, 4 * (oddWeightCount P.weight j : ℝ) /
                    Fintype.card P.weights) / 4 =
                  ∑ j : ι, (4 * (oddWeightCount P.weight j : ℝ) /
                    Fintype.card P.weights) / 4 := by
                      rw [Finset.sum_div]
              _ = ∑ j : ι, (oddWeightCount P.weight j : ℝ) /
                    Fintype.card P.weights := by
                  apply Finset.sum_congr rfl
                  intro j _hj
                  field_simp [ne_of_gt hcard]
              _ = (∑ j : ι, (oddWeightCount P.weight j : ℝ)) /
                    Fintype.card P.weights := by
                      rw [Finset.sum_div]
    _ ≤ (∑ ω : P.weights,
          (∑ j : ι, ε j * (P.weight ω j : ℝ)) ^ 2) /
          Fintype.card P.weights := by
            exact div_le_div_of_nonneg_right hraw hcard.le

/-- **Sharp `1/2` lower bound, squared form.**  If every coordinate sign flip
has normalized-HS distance at least `Δ`, then every diagonal local Lipschitz
square satisfies `L² ≥ d Δ²/4`. -/
theorem card_mul_signDetection_div_four_le_lipschitzSq
    (P : TorusWeightProfile ι) {Δsq Lsq : ℝ}
    (hdetect : P.DetectsCoordinateSigns Δsq)
    (hLip : P.HasDiagonalLipschitzSq Lsq) :
    Fintype.card ι * Δsq / 4 ≤ Lsq := by
  obtain ⟨ε, hε, hlow⟩ :=
    P.exists_sign_infinitesimalDistSq_ge_average_signFlipDistSq
  calc
    Fintype.card ι * Δsq / 4 = (∑ _j : ι, Δsq) / 4 := by simp
    _ ≤ (∑ j : ι, P.signFlipDistSq j) / 4 := by
      exact div_le_div_of_nonneg_right
        (Finset.sum_le_sum fun j _ ↦ hdetect j) (by norm_num)
    _ ≤ P.infinitesimalDistSq ε := hlow
    _ ≤ Lsq := hLip ε hε

end TorusWeightProfile

/-! ### The phase-cancelled Fock profile -/

/-- Indicator weight of a Fock basis subset. -/
def fockSubsetWeight {Y : Type*} [Fintype Y] [DecidableEq Y]
    (p : FockIndex Y) (j : Y) : ℤ :=
  if j ∈ p.2.val then 1 else 0

/-- Torus weight of the phase-cancelled Fock basis vector `(S,T)` is the
difference of the two subset indicators. -/
def exteriorAdWeight {Y : Type*} [Fintype Y] [DecidableEq Y]
    (p : FockIndex Y × FockIndex Y) (j : Y) : ℤ :=
  fockSubsetWeight p.1 j - fockSubsetWeight p.2 j

/-- The explicit weight profile of phase-cancelled fermionic Fock space. -/
def exteriorAdWeightProfile (Y : FiniteModel) : TorusWeightProfile Y where
  weights := doubleModel ⟨FockIndex Y, inferInstance, inferInstance⟩
  nonempty := by
    rw [card_doubleModel, card_FockIndex]
    positivity
  weight := exteriorAdWeight

/-- A coordinate of an exterior-adjoint weight is odd exactly when the two
subsets disagree on that coordinate. -/
theorem odd_exteriorAdWeight_iff
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (p : FockIndex Y × FockIndex Y) (j : Y) :
    Odd (exteriorAdWeight p j) ↔
      (j ∈ p.1.2.val) ≠ (j ∈ p.2.2.val) := by
  have hzero : ¬ Odd (0 : ℤ) := by
    intro ⟨k, hk⟩
    omega
  have hone : Odd (1 : ℤ) := ⟨0, by norm_num⟩
  have hnegOne : Odd (-1 : ℤ) := ⟨-1, by norm_num⟩
  unfold exteriorAdWeight fockSubsetWeight
  by_cases h₁ : j ∈ p.1.2.val <;> by_cases h₂ : j ∈ p.2.2.val <;>
    simp [h₁, h₂, hzero, hone, hnegOne]


/-! ## Actual fermionic upper bound and rank-one visibility -/

/-- The coordinate sign flip with a single `-1` entry. -/
def coordinateSignFlip (Y : FiniteModel) (j : Y) : Matrix Y Y ℂ :=
  Matrix.diagonal fun i ↦ if i = j then -1 else 1

theorem coordinateSignFlip_mem_unitaryGroup
    (Y : FiniteModel) (j : Y) :
    coordinateSignFlip Y j ∈ Matrix.unitaryGroup Y ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  rw [coordinateSignFlip, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  ext i k
  by_cases hik : i = k
  · subst k
    by_cases hij : i = j <;> simp [hij]
  · simp [hik]

/-- The midpoint determinant of a coordinate sign flip is zero: its `j`th
diagonal entry vanishes. -/
theorem det_midpoint_coordinateSignFlip_eq_zero
    (Y : FiniteModel) (j : Y) :
    (((2 : ℂ)⁻¹) • (1 + coordinateSignFlip Y j)).det = 0 := by
  have hdiag : (1 : Matrix Y Y ℂ) + coordinateSignFlip Y j =
      Matrix.diagonal (fun i ↦ 1 + if i = j then -1 else 1) := by
    ext i k
    simp [coordinateSignFlip, Matrix.one_apply]
    by_cases h : i = k <;> simp [h]
  rw [hdiag, ← Matrix.diagonal_smul, Matrix.det_diagonal]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp

/-- A single bad eigendirection becomes maximal normalized-HS separation
after phase-cancelled fermionic amplification. -/
theorem hsDistSq_exteriorAdMatrix_coordinateSignFlip
    (Y : FiniteModel) [LinearOrder Y] (j : Y) :
    hsDistSq (doubleModel (fockModel Y))
      (exteriorAdMatrix (coordinateSignFlip Y j))
      (exteriorAdMatrix 1) = 2 := by
  rw [hsDistSq_exteriorAdMatrix Y
    (coordinateSignFlip_mem_unitaryGroup Y j) (Submonoid.one_mem _)]
  rw [Matrix.conjTranspose_one, Matrix.mul_one,
    det_midpoint_coordinateSignFlip_eq_zero]
  norm_num

/-- **Global squared Lipschitz bound for fermionic amplification.**  The
phase-cancelled Fock representation pays at most the exact squared factor
`d/2` from operator norm to normalized Hilbert--Schmidt distance. -/
theorem hsDistSq_exteriorAdMatrix_le_card_mul_opNorm_sq_div_two
    (Y : FiniteModel) [LinearOrder Y] (hY : Nonempty Y)
    {A B : Matrix Y Y ℂ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ)
    (hB : B ∈ Matrix.unitaryGroup Y ℂ) :
    hsDistSq (doubleModel (fockModel Y))
        (exteriorAdMatrix A) (exteriorAdMatrix B) ≤
      Fintype.card Y * ‖A - B‖ ^ 2 / 2 := by
  have htwo : ‖A - B‖ ≤ 2 :=
    opNorm_sub_le_two_of_unitary hY hA hB
  exact hsDistSq_exteriorAdMatrix_le Y hA hB htwo le_rfl

/-- **Exact sharp constant at the weight-profile level.**  Any continuous
unitary representation whose torus weights give squared normalized-HS mass
at least `2` to every coordinate sign flip must have squared local
operator-to-HS cost at least `d/2`.

Classical torus weight decomposition turns an arbitrary finite-dimensional
continuous representation of `U(d)` into precisely such a profile. -/
theorem fermionic_squared_constant_is_universally_minimal
    {ι : Type*} [Fintype ι]
    (P : TorusWeightProfile ι) {Lsq : ℝ}
    (hdetect : P.DetectsCoordinateSigns 2)
    (hLip : P.HasDiagonalLipschitzSq Lsq) :
    Fintype.card ι / 2 ≤ Lsq := by
  have h := P.card_mul_signDetection_div_four_le_lipschitzSq hdetect hLip
  nlinarith

end

end GroupApproximation
