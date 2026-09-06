import GroupApproximation.GGT.DGOProposition414GeneralCharging

/-!
# Subdivision of the genuine general-parameter DGO least cost

Apply the proved balanced cut and component surgery to an extremal polygon.
The child witnesses use the original general parameters. The numerical output
is a subdivision of that least-cost function with logarithmic-square overhead.
-/

namespace GroupApproximation.GGT.DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w
variable {G : Type u} [Group G] {Λ : Type w}

/-- The general cost has the complete numerical subdivision data at a fixed
uniform chord radius. No component-surgery or metric producer remains assumed. -/
theorem exists_quasiCostSubdivisionData_atRadius
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (mu : ℝ) (b : ℕ)
    (hmu : 1 ≤ mu)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    (R : ℕ)
    (split : ∀ {n k : ℕ}, 8 ≤ n → n ≤ 2 ^ k →
      ∀ P : QuasiSumBoundInput D mu (b : ℝ) n,
        Nonempty (BalancedSplitData D hsymm P.word.length hδ P.bookkeeping k R))
    {n k : ℕ} (hn : 8 ≤ n) (hk : n ≤ 2 ^ k)
    (hquarter : ∀ L a c : ℕ,
      L ≤ 6 * (δ + 6) * (k + 1) + R → c < n →
      n ≤ 4 * (c - a) → 4 * (c - a) ≤ 3 * n →
      5 * ((c - a + 1) + L) ≤ 4 * n ∧
        5 * ((n - c) + a + 1 + L) ≤ 4 * n) :
    ∃ (childCount : ℕ) (childSides : Fin childCount → ℕ),
      childCount ≤ 2 * (6 * (δ + 6) * (k + 1) + R) + 2 ∧
      quasiSumCost D hsymm mu b hmu hδ n ≤
        ∑ i, quasiSumCost D hsymm mu b hmu hδ (childSides i) ∧
      n ≤ ∑ i, childSides i ∧
      (∑ i, childSides i) ≤ n + 6 *
        ((2 * (6 * (δ + 6) * (k + 1) + R) + 1) ^ 2) ∧
      (∀ i, 5 * childSides i ≤ 4 * n) := by
  classical
  by_cases hpos : 0 < quasiSumCost D hsymm mu b hmu hδ n
  · obtain ⟨P, hP⟩ := exists_extremal_quasiSumBoundInput_of_pos
      D hsymm mu b hmu hδ n hpos
    let B := Classical.choice (split hn hk P)
    let S := Classical.choice B.exists_gapCompletion
    let A := (B.gapIntervalsOfConfigurations S.components).toPathInput
    let e : (Fin B.brokenAssignment.index.first.pieceCount ⊕
        Fin B.brokenAssignment.index.second.pieceCount) ≃
        Fin (B.brokenAssignment.index.first.pieceCount +
          B.brokenAssignment.index.second.pieceCount) := finSumFinEquiv
    let side := Sum.elim (fun j => (A.first j).sideCount)
      (fun j => (A.second j).sideCount)
    let m := fun j => side (e.symm j)
    have hsum (f : ℕ → ℕ) : (∑ j, f (m j)) =
        (∑ j, f (A.first j).sideCount) + ∑ j, f (A.second j).sideCount := by
      calc
        (∑ j, f (m j)) = ∑ q, f (side q) :=
          Equiv.sum_comp e.symm (fun q => f (side q))
        _ = _ := by rw [Fintype.sum_sum_type]; rfl
    have hsumSides : (∑ j, m j) =
        (∑ j, (A.first j).sideCount) + ∑ j, (A.second j).sideCount := hsum id
    have hhalf := hquarter B.chord.length B.firstSide B.secondSide
      B.chord_length_le B.secondSide_lt B.quarter_lower B.quarter_upper
    refine ⟨_, m, ?_, ?_, ?_, ?_, ?_⟩
    · have hpieces := B.brokenAssignment.index.pieceCount_le
      have hchord := B.chord_length_le
      simp only [TwoHalfGreedyFamilyIndex.pieceCount] at hpieces
      omega
    · rw [hsum]
      obtain ⟨r, hr, hcost⟩ := P.hasRadiusWitness_of_gapCompletion hmu B S
      exact (hP r hr).trans hcost
    · rw [hsumSides]
      exact S.count_lower
    · rw [hsumSides]
      have hchord := B.chord_length_le
      have hscale : 2 * B.chord.length + 1 ≤
          2 * (6 * (δ + 6) * (k + 1) + R) + 1 := by omega
      exact S.count_upper.trans (Nat.add_le_add_left
        (Nat.mul_le_mul_left 6 (by simpa [pow_two] using Nat.mul_le_mul hscale hscale)) n)
    · intro j
      change 5 * side (e.symm j) ≤ 4 * n
      generalize hq : e.symm j = q
      cases q with
      | inl i =>
          exact (Nat.mul_le_mul_left 5
            (B.gapIntervalsOfConfigurations_first_side_bound S.components i)).trans hhalf.1
      | inr i =>
          exact (Nat.mul_le_mul_left 5
            (B.gapIntervalsOfConfigurations_second_side_bound S.components i)).trans hhalf.2
  · have hzero : quasiSumCost D hsymm mu b hmu hδ n = 0 := Nat.eq_zero_of_not_pos hpos
    let m : Fin 2 → ℕ := fun i => if i = 0 then n / 2 else n - n / 2
    have hsum : (∑ i, m i) = n := by
      rw [Fin.sum_univ_two]
      simp [m]
      omega
    refine ⟨2, m, by omega, ?_, by omega, by omega, ?_⟩
    · simp [hzero]
    · intro i
      fin_cases i <;> simp [m] <;> omega

end GroupApproximation.GGT.DGOProposition414

#audit_axioms GroupApproximation.GGT.DGOProposition414.exists_quasiCostSubdivisionData_atRadius
