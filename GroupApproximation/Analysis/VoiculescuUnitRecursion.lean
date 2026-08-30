import GroupApproximation.Analysis.VoiculescuPositiveUnit
import GroupApproximation.Analysis.VoiculescuQuasicentral
import GroupApproximation.Analysis.VoiculescuStrongToNorm
import GroupApproximation.Analysis.ShulmanDenseCompatibility

/-!
# The recursion that builds the monotone quasicentral unit

Everything the recursion needs is proved: the stage map
(`exists_improveUnit_stage_full`), the schedule (`stageTol`), and the positive
unit to draw from (`exists_positive_sequentialCompactUnit`).  This module runs
the recursion and records what each step achieves.  Assembling the clauses into
`MonotoneCompactUnit` is the next module.

## What is carried and what is not

The carrier is only `0 ≤ a ≤ 1` and compactness — the three facts the stage map
needs of its input.  The tolerance facts are *not* carried: they are recovered
afterwards from `Classical.choose_spec`, because the element produced at step
`j` is definitionally `improveUnit (eⱼ) (v _)`, so a statement about it is a
statement about the chosen index.  Carrying them would make the carrier depend
on `j` and every step a dependent rewrite; recovering them costs one `rfl`.

Monotonicity comes back the same way: `e_{j+1}` unfolds to `improveUnit eⱼ _`,
so `MonotoneStep.le_improveUnit` applies without the recursion recording it.

## Why the input is bundled

`PositiveQuasicentralUnit` carries the unit together with the three facts about
it that every stage uses.  Passing them as separate section hypotheses makes
Lean's variable inclusion decide, declaration by declaration, which of them
appear in a signature, and the resulting signatures do not agree.  One bundle
avoids that entirely.

## Why the compact family is empty

`stageNext` passes `∅` for the compact operators the stage map can also handle.
Norm absorption is not arranged directly; it comes at the end from strong
convergence and the landed `strongToNormOnCompacts`, which is why the vector
family carries the weight instead.  See `VoiculescuStageVector`.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The invariant the recursion carries: a positive compact contraction. -/
def StageCarrier (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : Type :=
  { a : H →L[ℂ] H // 0 ≤ a ∧ a ≤ 1 ∧ IsCompactOperator a }

/-- The input the recursion runs on: a sequential approximate unit for the
compacts whose members are positive contractions and which is asymptotically
central for the given family. -/
structure PositiveQuasicentralUnit (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (S : ℕ → (H →L[ℂ] H)) where
  /-- The underlying sequential unit. -/
  toUnit : SequentialCompactUnit H
  /-- Its members are positive. -/
  nonneg : ∀ n, 0 ≤ toUnit.toFun n
  /-- Its members are below the identity. -/
  le_one : ∀ n, toUnit.toFun n ≤ 1
  /-- It is asymptotically central for the family. -/
  quasicentral : ∀ k,
    Tendsto (fun n ↦ ‖toUnit.toFun n * S k - S k * toUnit.toFun n‖) atTop (𝓝 0)

/-- **The input exists** wherever the landed (V1) does: square its members. -/
theorem nonempty_positiveQuasicentralUnit (u : SequentialCompactUnit H)
    (S : ℕ → (H →L[ℂ] H))
    (hq : ∀ k, Tendsto (fun n ↦ ‖u.toFun n * S k - S k * u.toFun n‖) atTop (𝓝 0)) :
    Nonempty (PositiveQuasicentralUnit H S) := by
  obtain ⟨w, hw0, hw1, hwq⟩ := exists_positive_sequentialCompactUnit u S hq
  exact ⟨⟨w, hw0, hw1, hwq⟩⟩

variable {S : ℕ → (H →L[ℂ] H)} (p : PositiveQuasicentralUnit H S) (x : ℕ → H)

/-- The existential the stage map hands the recursion at step `j`. -/
theorem stageExists (j : ℕ) (c : StageCarrier H) :
    ∃ n, (∀ k ∈ Finset.range (j + 2),
        ‖improveUnit c.1 (p.toUnit.toFun n) * S k
          - S k * improveUnit c.1 (p.toUnit.toFun n)‖ < stageTol S (j + 1)) ∧
      (∀ i ∈ (∅ : Finset ℕ),
        ‖(0 : H →L[ℂ] H) - improveUnit c.1 (p.toUnit.toFun n) * 0‖
          < stageTol S (j + 1)) ∧
      ∀ i ∈ Finset.range (j + 1),
        ‖x i - improveUnit c.1 (p.toUnit.toFun n) (x i)‖ < stageTol S (j + 1) :=
  exists_improveUnit_stage_full p.toUnit c.2.2.1 c.2.2.2 S (fun _ ↦ (0 : H →L[ℂ] H))
    (fun _ ↦ isCompactOperator_zero) x (Finset.range (j + 2)) ∅ (Finset.range (j + 1))
    p.quasicentral (stageTol_pos S (j + 1))

/-- The index the stage map selects at step `j`. -/
def stageIndex (j : ℕ) (c : StageCarrier H) : ℕ := (stageExists p x j c).choose

/-- One step of the recursion. -/
def stageNext (j : ℕ) (c : StageCarrier H) : StageCarrier H :=
  ⟨improveUnit c.1 (p.toUnit.toFun (stageIndex p x j c)),
    improveUnit_nonneg c.2.1 (p.nonneg _),
    improveUnit_le_one c.2.2.1 (p.le_one _),
    isCompactOperator_improveUnit c.2.2.2 (p.toUnit.isCompact _)⟩

/-- The recursion. -/
def stageSeq : ℕ → StageCarrier H
  | 0 => ⟨0, le_rfl, zero_le_one, isCompactOperator_zero⟩
  | (j + 1) => stageNext p x j (stageSeq j)

/-- The sequence the recursion builds. -/
def stageUnit (j : ℕ) : H →L[ℂ] H := (stageSeq p x j).1

theorem stageUnit_zero : stageUnit p x 0 = 0 := rfl

theorem stageUnit_nonneg (j : ℕ) : 0 ≤ stageUnit p x j := (stageSeq p x j).2.1

theorem stageUnit_le_one (j : ℕ) : stageUnit p x j ≤ 1 := (stageSeq p x j).2.2.1

theorem stageUnit_isCompact (j : ℕ) : IsCompactOperator (stageUnit p x j) :=
  (stageSeq p x j).2.2.2

theorem stageUnit_succ (j : ℕ) :
    stageUnit p x (j + 1)
      = improveUnit (stageUnit p x j)
        (p.toUnit.toFun (stageIndex p x j (stageSeq p x j))) := rfl

theorem stageUnit_le_succ (j : ℕ) : stageUnit p x j ≤ stageUnit p x (j + 1) := by
  rw [stageUnit_succ]
  exact le_improveUnit (p.nonneg _)

theorem stageUnit_monotone : Monotone (stageUnit p x) :=
  monotone_nat_of_le_succ (stageUnit_le_succ p x)

/-! ## What each step achieves -/

theorem stageUnit_norm_commutator_lt {j k : ℕ} (hk : k ≤ j) :
    ‖stageUnit p x j * S k - S k * stageUnit p x j‖ < stageTol S j := by
  cases j with
  | zero =>
      rw [Nat.le_zero] at hk
      subst hk
      rw [stageUnit_zero, zero_mul, mul_zero, sub_self, norm_zero]
      exact stageTol_pos S 0
  | succ j =>
      exact (stageExists p x j (stageSeq p x j)).choose_spec.1 k
        (Finset.mem_range.mpr (by omega))

theorem stageUnit_norm_sub_apply_lt {j i : ℕ} (hi : i ≤ j) :
    ‖x i - stageUnit p x (j + 1) (x i)‖ < stageTol S (j + 1) :=
  (stageExists p x j (stageSeq p x j)).choose_spec.2.2 i
    (Finset.mem_range.mpr (by omega))

/-! ## Assembly into the strengthened approximate unit -/

/-- The recursion converges to the identity on every vector of the sequence it
was asked to control. -/
theorem tendsto_stageUnit_norm_sub_dense (i : ℕ) :
    Tendsto (fun n ↦ ‖stageUnit p x n (x i) - x i‖) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (tendsto_stageTol S) ε hε
  refine ⟨max N (i + 1), fun n hn ↦ ?_⟩
  have hNn : N ≤ n := (le_max_left _ _).trans hn
  have hin : i ≤ n - 1 := by omega
  have hnpos : 0 < n := by omega
  have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have hb := stageUnit_norm_sub_apply_lt p x (j := n - 1) (i := i) hin
  rw [hnsub] at hb
  have ht := hN n hNn
  have ht' : stageTol S n < ε := by
    simpa [Real.dist_eq, abs_of_pos (stageTol_pos S n)] using ht
  have hfinal := hb.trans ht'
  simpa [Real.dist_eq, norm_sub_rev, abs_of_nonneg (norm_nonneg _)] using hfinal

/-- Control on a dense sequence and the uniform contraction bound upgrade the
recursion to strong convergence on the whole Hilbert space. -/
theorem tendsto_stageUnit_apply_of_dense (hdense : DenseRange x) (z : H) :
    Tendsto (fun n ↦ stageUnit p x n z) atTop (𝓝 z) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply ShulmanDenseCompatibility.tendsto_norm_sub_of_dense
    (fun n z ↦ stageUnit p x n z) (fun _ z ↦ z)
  · intro z y
    simpa using tendsto_const_nhds
  · intro z y
    simpa using tendsto_const_nhds
  · intro n y
    exact le_trans ((stageUnit p x n).le_opNorm y)
      (by
        calc
          ‖stageUnit p x n‖ * ‖y‖ ≤ 1 * ‖y‖ :=
            mul_le_mul_of_nonneg_right
              (norm_le_one_of_nonneg_of_le_one (stageUnit_nonneg p x n)
                (stageUnit_le_one p x n)) (norm_nonneg y)
          _ = ‖y‖ := one_mul _)
  · intro _ y
    exact le_rfl
  · exact hdense
  · rintro _ ⟨i, rfl⟩
    exact tendsto_stageUnit_norm_sub_dense p x i

/-- The recursive sequence, bundled as an approximate unit for the compacts. -/
noncomputable def stageSequentialCompactUnit (hdense : DenseRange x) :
    SequentialCompactUnit H where
  toFun := stageUnit p x
  isCompact := stageUnit_isCompact p x
  isSelfAdjoint := fun n ↦ IsSelfAdjoint.of_nonneg (stageUnit_nonneg p x n)
  norm_le := fun n ↦ norm_le_one_of_nonneg_of_le_one (stageUnit_nonneg p x n)
    (stageUnit_le_one p x n)
  tendsto_left := fun T hT ↦ strongToNormOnCompacts H (stageUnit p x)
    (fun n ↦ norm_le_one_of_nonneg_of_le_one (stageUnit_nonneg p x n)
      (stageUnit_le_one p x n))
    (tendsto_stageUnit_apply_of_dense p x hdense) T hT

/-- The same sequence with the order and zero-start clauses needed by the
partition construction. -/
noncomputable def stageMonotoneCompactUnit (hdense : DenseRange x) :
    MonotoneCompactUnit H where
  toSequentialCompactUnit := stageSequentialCompactUnit p x hdense
  nonneg := stageUnit_nonneg p x
  le_one := stageUnit_le_one p x
  mono := stageUnit_monotone p x
  zero := stageUnit_zero p x

/-- The recursive unit is asymptotically central for every target. -/
theorem tendsto_stageUnit_commutator (k : ℕ) :
    Tendsto (fun n ↦ ‖stageUnit p x n * S k - S k * stageUnit p x n‖)
      atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (tendsto_stageTol S) ε hε
  refine ⟨max N k, fun n hn ↦ ?_⟩
  have hNn : N ≤ n := (le_max_left _ _).trans hn
  have hkn : k ≤ n := (le_max_right _ _).trans hn
  have hb := stageUnit_norm_commutator_lt p x hkn
  have ht := hN n hNn
  have ht' : stageTol S n < ε := by
    simpa [Real.dist_eq, abs_of_pos (stageTol_pos S n)] using ht
  have hfinal := hb.trans ht'
  simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hfinal

/-- The square root of each successive piece has the geometric commutator
bound selected by the schedule. -/
theorem stagePieceSqrt_norm_commutator_lt {j k : ℕ} (hk : k ≤ j)
    (hdense : DenseRange x) :
    ‖(stageMonotoneCompactUnit p x hdense).pieceSqrt j * S k -
        S k * (stageMonotoneCompactUnit p x hdense).pieceSqrt j‖
      < (1 : ℝ) / 2 ^ j := by
  let u := stageMonotoneCompactUnit p x hdense
  apply norm_commutator_sqrt_piece_lt S hk (u.piece_nonneg j) (u.piece_le_one j)
  have hj := stageUnit_norm_commutator_lt p x hk
  have hj1 := stageUnit_norm_commutator_lt p x (hk.trans (Nat.le_succ j))
  have hj1' :
      ‖stageUnit p x (j + 1) * S k - S k * stageUnit p x (j + 1)‖
        < stageTol S j :=
    hj1.trans_le (stageTol_antitone S (Nat.le_succ j))
  have hid :
      (u.piece j) * S k - S k * (u.piece j) =
        (stageUnit p x (j + 1) * S k - S k * stageUnit p x (j + 1)) -
          (stageUnit p x j * S k - S k * stageUnit p x j) := by
    change
      (stageUnit p x (j + 1) - stageUnit p x j) * S k -
          S k * (stageUnit p x (j + 1) - stageUnit p x j) = _
    noncomm_ring
  rw [hid]
  exact (norm_sub_le _ _).trans_lt (by linarith)

/-- The geometric tail bound makes the square-root commutators summable. -/
theorem summable_stagePieceSqrt_commutator (k : ℕ) (hdense : DenseRange x) :
    Summable fun j ↦
      ‖(stageMonotoneCompactUnit p x hdense).pieceSqrt j * S k -
        S k * (stageMonotoneCompactUnit p x hdense).pieceSqrt j‖ := by
  rw [← summable_nat_add_iff k]
  refine Summable.of_nonneg_of_le (fun j ↦ norm_nonneg _) (fun j ↦ ?_)
    ((summable_geometric_two).mul_left ((1 / 2 : ℝ) ^ k))
  have hb := stagePieceSqrt_norm_commutator_lt p x (j := j + k) (k := k)
    (Nat.le_add_left k j) hdense
  exact hb.le.trans_eq (by rw [pow_add]; ring)

/-- **The recursion closes (V1c).**  It produces the positive increasing unit,
strong/norm absorption, asymptotic centrality, and the summable square-root
commutators consumed by the partition construction. -/
theorem monotoneQuasicentralStatement : MonotoneQuasicentralStatement := by
  intro K _ _ _ _ S
  obtain ⟨e, heK, heSA, heNorm, heComm, heAbs⟩ :=
    quasicentralApproximateUnitSeparable K S
  let base : SequentialCompactUnit K :=
    { toFun := e
      isCompact := heK
      isSelfAdjoint := heSA
      norm_le := heNorm
      tendsto_left := heAbs }
  obtain ⟨p⟩ := nonempty_positiveQuasicentralUnit base S heComm
  let x : ℕ → K := TopologicalSpace.denseSeq K
  have hx : DenseRange x := TopologicalSpace.denseRange_denseSeq K
  exact ⟨stageMonotoneCompactUnit p x hx,
    tendsto_stageUnit_commutator p x,
    fun k ↦ summable_stagePieceSqrt_commutator p x k hx⟩

end

end ShulmanFill
end GroupApproximation
