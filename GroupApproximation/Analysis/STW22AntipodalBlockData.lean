import GroupApproximation.Analysis.AntipodalBlockTraceWitness
import GroupApproximation.Analysis.STW22CounterexampleAssembly

/-!
# Concrete antipodal block data for STW Problem XXII

This file assembles the real-projective fixed-point blocks into the exact
`CoordinateStateBlockData` consumed by the compactness proof.  All operator
algebraic work is unconditional.  The single remaining topology input is
`ComplexOddMapCommonZero`: the standard Borsuk--Ulam zero theorem for a
continuous odd map from a real sphere to a finite-dimensional complex vector
space.
-/

namespace GroupApproximation
namespace STW22

open Filter PolarLiftingGeneralCStar
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open CStarState CuntzPedersenCoronaObstruction
open CoronaCoordinateStateCompactness UniformTracialGNSTwoGauge
open UniformTracialTwoNullIdeal
open STW22Assembly

open scoped CStarAlgebra ComplexOrder Matrix

noncomputable section

/-! ## The exact topological residue -/

/-- The complex-coordinate form of Borsuk--Ulam used by the concrete blocks.
An odd continuous map `S^d → ℂ^κ` has a zero when its real target dimension
`2 * card κ` is at most `d`. -/
def ComplexOddMapCommonZero : Prop :=
  ∀ (d : ℕ) (κ : Type) (_ : Finite κ), 2 * Nat.card κ ≤ d →
    ∀ f : C(Sphere d, κ → ℂ),
      (∀ x : Sphere d, f (-x) = -f x) →
      ∃ x : Sphere d, f x = 0

/-! ## The corner-state computation -/

/-- If both off-diagonal parts of the distinguished row and column vanish,
the distinguished vector state annihilates the self-commutator. -/
theorem trivialLineState_selfCommutator_eq_zero_of_offDiagonal
    {d s : ℕ} (z : RealProjectiveBlock d s) (x : Sphere d)
    (hcol : ∀ k : Fin s, z.1 x k.succ 0 = 0)
    (hrow : ∀ k : Fin s, z.1 x 0 k.succ = 0) :
    (trivialLineState d s x).toCLM (selfCommutator z) = 0 := by
  rw [trivialLineState_apply]
  change (star (z.1 x) * z.1 x) 0 0 -
    (z.1 x * star (z.1 x)) 0 0 = 0
  rw [CStarMatrix.mul_apply, CStarMatrix.mul_apply]
  apply sub_eq_zero.mpr
  apply Finset.sum_congr rfl
  intro k _
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k, rfl⟩
  · exact mul_comm _ _
  · simp [CStarMatrix.star_apply, hcol k, hrow k]

/-- A common zero of the simultaneous row-and-column map gives a single state
which detects the witness and annihilates every displayed self-commutator. -/
theorem exists_trivialLineState_constraints_of_simultaneous_zero
    {ι : Type*} {d s : ℕ} (z : ι → RealProjectiveBlock d s)
    (x : Sphere d) (hx : simultaneousOffDiagonalMap z x = 0) :
    ∃ ψ : State (RealProjectiveBlock d s),
      ψ.toCLM (blockWitness d s) = 1 ∧
      ∀ i : ι, ψ.toCLM (selfCommutator (z i)) = 0 := by
  obtain ⟨hcol, hrow⟩ :=
    offDiagonal_entries_eq_zero_of_simultaneous_eq_zero z hx
  refine ⟨trivialLineState d s x, trivialLineState_blockWitness d s x, ?_⟩
  intro i
  exact trivialLineState_selfCommutator_eq_zero_of_offDiagonal
    (z i) x (hcol i) (hrow i)

/-! ## A quadratic block schedule -/

/-- The complementary rank at coordinate `n`; starting at one avoids the
degenerate inverse in the diagonal witness. -/
def antipodalBlockSize (n : ℕ) : ℕ := n + 1

/-- The sphere dimension.  The simultaneous target for `m` block elements has
complex dimension `2*m*s`, hence real dimension `4*m*s`; this choice handles
every `m ≤ s`. -/
def antipodalBlockDimension (n : ℕ) : ℕ :=
  4 * antipodalBlockSize n * antipodalBlockSize n

/-- The concrete coordinate C-star algebras. -/
abbrev AntipodalCounterexampleBlock (n : ℕ) : Type :=
  RealProjectiveBlock (antipodalBlockDimension n) (antipodalBlockSize n)

instance nonemptyTracialState_antipodalCounterexampleBlock (n : ℕ) :
    Nonempty (TracialState (AntipodalCounterexampleBlock n)) :=
  nonemptyTracialState_realProjectiveBlock
    (antipodalBlockDimension n) (antipodalBlockSize n)

/-- The actual coordinate gauge, packaged once with the explicit family of
nonempty tracial-state spaces. -/
def antipodalAllTracesGauge : TracialTwoGauge AntipodalCounterexampleBlock := by
  exact @allTracesTracialTwoGauge AntipodalCounterexampleBlock inferInstance
    inferInstance (fun n ↦ nonemptyTracialState_antipodalCounterexampleBlock n)

/-! ## Uniform operator-norm boundedness -/

/-- The diagonal involution has norm one. -/
theorem norm_blockInvolution (s : ℕ) : ‖blockInvolution s‖ = 1 := by
  have hstar : star (blockInvolution s) * blockInvolution s = 1 := by
    rw [blockInvolution_star, blockInvolution_sq]
  have hnorm : ‖star (blockInvolution s) * blockInvolution s‖ =
      ‖blockInvolution s‖ ^ 2 := by
    simpa [pow_two] using
      (CStarRing.norm_star_mul_self (x := blockInvolution s))
  rw [hstar, norm_one] at hnorm
  nlinarith [norm_nonneg (blockInvolution s)]

/-- The projection onto the trivial coordinate is contractive. -/
theorem norm_trivialProjectionMatrix_le_one (s : ℕ) :
    ‖trivialProjectionMatrix s‖ ≤ 1 := by
  rw [trivialProjectionMatrix, norm_smul]
  have hscalar : ‖((2 : ℂ)⁻¹)‖ = (1 / 2 : ℝ) := by norm_num
  rw [hscalar]
  have hadd := norm_add_le (1 : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ)
    (blockInvolution s)
  rw [norm_one, norm_blockInvolution] at hadd
  nlinarith

/-- A fixed bound, independent of the complementary rank, for the diagonal
witness.  Exact norm one is unnecessary for bounded-product membership. -/
theorem norm_witnessMatrix_le_three (s : ℕ) (hs : 1 ≤ s) :
    ‖witnessMatrix s‖ ≤ 3 := by
  have hp := norm_trivialProjectionMatrix_le_one s
  have hsub : ‖(1 : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ) -
      trivialProjectionMatrix s‖ ≤ 2 := by
    calc
      ‖(1 : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ) -
          trivialProjectionMatrix s‖
          ≤ ‖(1 : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ)‖ +
            ‖trivialProjectionMatrix s‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (le_of_eq norm_one) hp
      _ = 2 := by norm_num
  have hsnorm : 1 ≤ ‖(s : ℂ)‖ := by
    simpa using hs
  have hinv : ‖((s : ℂ)⁻¹)‖ ≤ 1 := by
    rw [norm_inv]
    exact (inv_le_one₀ (zero_lt_one.trans_le hsnorm)).2 hsnorm
  rw [witnessMatrix]
  calc
    ‖trivialProjectionMatrix s -
        (s : ℂ)⁻¹ • (1 - trivialProjectionMatrix s)‖
        ≤ ‖trivialProjectionMatrix s‖ +
          ‖(s : ℂ)⁻¹ • (1 - trivialProjectionMatrix s)‖ := norm_sub_le _ _
    _ = ‖trivialProjectionMatrix s‖ +
        ‖((s : ℂ)⁻¹)‖ * ‖(1 : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ) -
          trivialProjectionMatrix s‖ := by rw [norm_smul]
    _ ≤ 1 + 1 * 2 := add_le_add hp (mul_le_mul hinv hsub (norm_nonneg _) zero_le_one)
    _ = 3 := by norm_num

/-- The same uniform bound for the constant block section. -/
theorem norm_blockWitness_le_three (d s : ℕ) (hs : 1 ≤ s) :
    ‖blockWitness d s‖ ≤ 3 := by
  change ‖(blockWitness d s).1‖ ≤ 3
  apply (ContinuousMap.norm_le _ (by norm_num)).2
  intro x
  simpa [blockWitness] using norm_witnessMatrix_le_three s hs

/-- The concrete bounded sequence of diagonal witnesses. -/
def antipodalWitnessSequence :
    BoundedCStarSequence AntipodalCounterexampleBlock :=
  ⟨fun n ↦ blockWitness (antipodalBlockDimension n) (antipodalBlockSize n),
    memℓp_infty ⟨3, by
      rintro _ ⟨n, rfl⟩
      exact norm_blockWitness_le_three _ _ (by simp [antipodalBlockSize])⟩⟩

@[simp] theorem antipodalWitnessSequence_apply (n : ℕ) :
    antipodalWitnessSequence n =
      blockWitness (antipodalBlockDimension n) (antipodalBlockSize n) := rfl

/-- Borsuk--Ulam supplies a simultaneous row-and-column zero for any family
of at most `s` elements at coordinate `s-1`. -/
theorem exists_simultaneousOffDiagonal_zero
    (hBU : ComplexOddMapCommonZero) {n m : ℕ}
    (hm : m ≤ antipodalBlockSize n)
    (z : Fin m → AntipodalCounterexampleBlock n) :
    ∃ x : Sphere (antipodalBlockDimension n),
      simultaneousOffDiagonalMap z x = 0 := by
  let f := simultaneousOffDiagonalMap z
  have hcard : 2 * Nat.card (OffDiagonalIndex (Fin m) (antipodalBlockSize n)) ≤
      antipodalBlockDimension n := by
    simp only [OffDiagonalIndex, Nat.card_prod, Nat.card_fin, Nat.card_sum]
    dsimp only [antipodalBlockDimension]
    calc
      2 * (m * (antipodalBlockSize n + antipodalBlockSize n)) =
          4 * m * antipodalBlockSize n := by ring
      _ ≤ 4 * antipodalBlockSize n * antipodalBlockSize n := by
        exact Nat.mul_le_mul_right (antipodalBlockSize n)
          (Nat.mul_le_mul_left 4 hm)
  exact hBU (antipodalBlockDimension n)
    (OffDiagonalIndex (Fin m) (antipodalBlockSize n)) inferInstance hcard f
    (simultaneousOffDiagonalMap_neg z)

/-- The finite coordinate-state constraints at one sufficiently large
coordinate, with both off-diagonal corners zeroed. -/
theorem exists_coordinateState_constraints
    (hBU : ComplexOddMapCommonZero) {n m : ℕ}
    (hm : m ≤ antipodalBlockSize n)
    (z : Fin m → AntipodalCounterexampleBlock n) :
    ∃ ψ : State (AntipodalCounterexampleBlock n),
      ψ.toCLM (blockWitness (antipodalBlockDimension n)
        (antipodalBlockSize n)) = 1 ∧
      ∀ i : Fin m, ψ.toCLM (selfCommutator (z i)) = 0 := by
  obtain ⟨x, hx⟩ := exists_simultaneousOffDiagonal_zero hBU hm z
  exact exists_trivialLineState_constraints_of_simultaneous_zero z x hx

/-- Any bounded sequence whose coordinates are the concrete witnesses has the
arbitrarily-late state constraints required by the corona compactness theorem.
This is the complete passage from the one-coordinate Borsuk--Ulam zero to the
quantification over finite sets of bounded sequences. -/
theorem arbitrarilyLateCoordinateStateConstraints_of_witnessSequence
    (hBU : ComplexOddMapCommonZero)
    (h : BoundedCStarSequence AntipodalCounterexampleBlock)
    (hh : ∀ n, h n = blockWitness (antipodalBlockDimension n)
      (antipodalBlockSize n)) :
    ArbitrarilyLateCoordinateStateConstraints h := by
  intro S floor
  let n := max floor S.card
  let z : Fin S.card → AntipodalCounterexampleBlock n := fun i ↦
    ((S.equivFin.symm i : S) : BoundedCStarSequence
      AntipodalCounterexampleBlock) n
  have hm : S.card ≤ antipodalBlockSize n := by
    dsimp only [n, antipodalBlockSize]
    omega
  obtain ⟨ψ, hψw, hψz⟩ := exists_coordinateState_constraints hBU hm z
  refine ⟨n, le_max_left _ _, ψ, ?_, ?_⟩
  · rw [hh]
    exact hψw
  · intro a ha
    let i : Fin S.card := S.equivFin ⟨a, ha⟩
    have hi : S.equivFin.symm i = ⟨a, ha⟩ :=
      S.equivFin.symm_apply_apply ⟨a, ha⟩
    have hz := hψz i
    change ψ.toCLM (selfCommutator (a n)) = 0
    simpa only [z, hi] using hz

/-- The concrete witness sequence has the exact coordinate-state property
required by the compactness route. -/
theorem antipodalWitness_arbitrarilyLateCoordinateStateConstraints
    (hBU : ComplexOddMapCommonZero) :
    ArbitrarilyLateCoordinateStateConstraints antipodalWitnessSequence :=
  arbitrarilyLateCoordinateStateConstraints_of_witnessSequence hBU
    antipodalWitnessSequence (fun _ ↦ rfl)

/-! ## The actual all-traces gauge -/

/-- The exact uniform tracial two-size of the witness in coordinate `n`. -/
def antipodalTwoRate (n : ℕ) : ℝ :=
  Real.sqrt (((n : ℝ) + 1)⁻¹)

/-- The exact rate tends to zero. -/
theorem antipodalTwoRate_tendsto_zero :
    Tendsto antipodalTwoRate atTop (nhds 0) := by
  have htop : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 1))
      atTop (nhds 0) := htop.const_div_atTop 1
  have hs := hinv.sqrt
  change Tendsto (fun n : ℕ ↦ Real.sqrt (((n : ℝ) + 1)⁻¹)) atTop (nhds 0)
  simpa only [one_div, Real.sqrt_zero] using hs

/-- At every coordinate, the actual supremum over all bundled tracial states
is the explicit rate `sqrt (1/(n+1))`. -/
theorem allTracesGauge_antipodalWitnessSequence (n : ℕ) :
    antipodalAllTracesGauge.q n
        (antipodalWitnessSequence n) = antipodalTwoRate n := by
  rw [antipodalAllTracesGauge]
  change UniformTracialSequenceCompletion.tracialTwoSize n
    (antipodalWitnessSequence n) = antipodalTwoRate n
  rw [antipodalWitnessSequence_apply,
    tracialTwoSize_blockWitness antipodalBlockDimension antipodalBlockSize n
      (by simp [antipodalBlockSize])]
  simp [antipodalBlockSize, antipodalTwoRate]

/-- All nontopological fields of the concrete counterexample block package.
The displayed `hBU` is the sole remaining input and is isolated in
`ComplexOddMapCommonZero` above. -/
def antipodalCoordinateStateBlockData (hBU : ComplexOddMapCommonZero) :
    CoordinateStateBlockData AntipodalCounterexampleBlock
      antipodalAllTracesGauge where
  seq := antipodalWitnessSequence
  gauge_tendsto_zero := by
    simpa only [allTracesGauge_antipodalWitnessSequence] using
      antipodalTwoRate_tendsto_zero
  coordinate_states :=
    antipodalWitness_arbitrarilyLateCoordinateStateConstraints hBU

end

end STW22
end GroupApproximation
