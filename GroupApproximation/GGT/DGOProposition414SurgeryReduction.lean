import GroupApproximation.GGT.DGOProposition414BalancedSurgery

/-!
# The balanced-surgery input to DGO Proposition 4.14

This module removes the extremal polygon and balanced split from the public
component-surgery premise.  A producer only has to realize the interval
surgery attached to an arbitrary raw balanced split.  The reduction itself
chooses an extremal input (including the zero-cost case), constructs its
balanced split, and exports the numerical subdivision tuple consumed by the
corrected Proposition 4.14 assembly.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- The two dependent objects which remain to be constructed by interval
surgery on a fixed raw balanced split. -/
structure BalancedSplitSurgeryRealization
    (D : RelGenSet G Λ) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {n : ℕ} (P : SumBoundInput D (b : ℝ) n) {k R : ℕ}
    (B : BalancedSplitData D hsymm b hδ P k R) where
  surgery : BalancedSplitIntervalSurgery D hsymm b hδ P B
  embedding : BalancedSplitTargetEmbedding D hsymm b hδ P B surgery

/-- The exact subdivision output at a fixed uniform balanced-split radius.

Besides the five facts consumed by the quadratic subdivision assembly, this
version retains the canonical bounds on the number of children and on the
flattened traversal scale. -/
theorem exists_quadraticCostSubdivisionData_of_balancedSurgeryAtRadius
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    (produce : ∀ {n k R : ℕ} (P : SumBoundInput D (b : ℝ) n)
      (B : BalancedSplitData D hsymm b hδ P k R),
        Nonempty (BalancedSplitSurgeryRealization D hsymm b hδ P B))
    (R : ℕ)
    (split : ∀ {n k : ℕ}, 8 ≤ n → n ≤ 2 ^ k →
      ∀ P : SumBoundInput D (b : ℝ) n,
        Nonempty (BalancedSplitData D hsymm b hδ P k R))
    {n k : ℕ} (hn : 8 ≤ n) (hk : n ≤ 2 ^ k) :
    ∃ (childCount : ℕ) (childSides : Fin childCount → ℕ)
        (chordLength : ℕ) (partners : List ℕ),
      childCount ≤ 2 * (6 * (δ + 6) * (k + 1) + R) + 2 ∧
      chordLength ≤ 2 * (6 * (δ + 6) * (k + 1) + R) + 1 ∧
      sumCost D hsymm b hδ n ≤
        ∑ i, sumCost D hsymm b hδ (childSides i) ∧
      n ≤ ∑ i, childSides i ∧
      (ChordPartnerQuadraticTraversalBound chordLength partners →
        ∑ i, childSides i ≤ n + 6 * (chordLength * chordLength)) ∧
      (∀ i, 5 * childSides i ≤ 4 * n) ∧
      ChordPartnerQuadraticTraversalBound chordLength partners := by
  by_cases hpos : 0 < sumCost D hsymm b hδ n
  · obtain ⟨P, hP⟩ :=
      exists_extremal_sumBoundInput_of_pos D hsymm b hδ n hpos
    let B := Classical.choice (split hn hk P)
    let realization := Classical.choice (produce P B)
    let A := realization.embedding.certificate
    refine ⟨A.k, A.childSides, A.chordLength, A.partners, ?_, ?_, ?_,
      A.count_lower, A.count_upper, A.child_small, A.traversal⟩
    · change B.brokenAssignment.index.first.pieceCount +
          B.brokenAssignment.index.second.pieceCount ≤
        2 * (6 * (δ + 6) * (k + 1) + R) + 2
      have hpieces := B.brokenAssignment.index.pieceCount_le
      have hchord := B.chord_length_le
      simp only [TwoHalfGreedyFamilyIndex.pieceCount] at hpieces
      omega
    · change 2 * B.chord.length + 1 ≤
        2 * (6 * (δ + 6) * (k + 1) + R) + 1
      have hchord := B.chord_length_le
      omega
    · exact sumCost_le_childCosts_of_extremalCertificate D hsymm b hδ P hP A
  · have hzero : sumCost D hsymm b hδ n = 0 := Nat.eq_zero_of_not_pos hpos
    let m : Fin 2 → ℕ := fun i => if i = 0 then n / 2 else n - n / 2
    have hsum : (∑ i, m i) = n := by
      rw [Fin.sum_univ_two]
      simp [m]
      omega
    refine ⟨2, m, 0, [], by omega, by omega, ?_, by omega, ?_, ?_, ?_⟩
    · simp [hzero]
    · intro _
      omega
    · intro i
      fin_cases i <;> simp [m] <;> omega
    · simp [ChordPartnerQuadraticTraversalBound, chordTraversalCost]

/-- The exact subdivision output of balanced interval surgery, with the
extremal polygon and raw balanced split chosen internally.

The sole geometric premise is a realization for every raw split.  In
particular, callers no longer supply a polygon, an extremality proof, a split,
a component placement, or a broken-component assignment. -/
theorem exists_quadraticCostSubdivisionData_of_balancedSurgery
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    (produce : ∀ {n k R : ℕ} (P : SumBoundInput D (b : ℝ) n)
      (B : BalancedSplitData D hsymm b hδ P k R),
        Nonempty (BalancedSplitSurgeryRealization D hsymm b hδ P B))
    {n k : ℕ} (hn : 8 ≤ n) (hk : n ≤ 2 ^ k) :
    ∃ (childCount : ℕ) (childSides : Fin childCount → ℕ)
        (chordLength : ℕ) (partners : List ℕ),
      sumCost D hsymm b hδ n ≤
        ∑ i, sumCost D hsymm b hδ (childSides i) ∧
      n ≤ ∑ i, childSides i ∧
      (ChordPartnerQuadraticTraversalBound chordLength partners →
        ∑ i, childSides i ≤ n + 6 * (chordLength * chordLength)) ∧
      (∀ i, 5 * childSides i ≤ 4 * n) ∧
      ChordPartnerQuadraticTraversalBound chordLength partners := by
  obtain ⟨R, hR⟩ := exists_balancedSplitData D hsymm b hδ
  obtain ⟨childCount, childSides, chordLength, partners, _hcount, _hchord,
    hcost, hlower, hupper, hsmall, htraversal⟩ :=
    exists_quadraticCostSubdivisionData_of_balancedSurgeryAtRadius
      D hsymm b hδ produce R hR hn hk
  exact ⟨childCount, childSides, chordLength, partners, hcost, hlower,
    hupper, hsmall, htraversal⟩

/-! ## Direct connection to the Proposition 4.14 reduction -/

/-- The uniform bound for the raw cutting chord when the dyadic exponent is
chosen to be `log₂ n + 1`. -/
def balancedSurgeryChordCap (δ R n : ℕ) : ℕ :=
  6 * (δ + 6) * (Nat.log 2 n + 2) + R

/-- The real-valued child-count overhead exported by balanced surgery. -/
def balancedSurgeryPieceOverhead (δ R : ℕ) (n : ℕ) : ℝ :=
  (2 * balancedSurgeryChordCap δ R n + 2 : ℕ)

/-- The real-valued quadratic traversal overhead exported by the flattened
two-half family. -/
def balancedSurgerySizeOverhead (δ R : ℕ) (n : ℕ) : ℝ :=
  (6 * ((2 * balancedSurgeryChordCap δ R n + 1) *
    (2 * balancedSurgeryChordCap δ R n + 1)) : ℕ)

/-- Proposition 4.14 from balanced interval surgery and the explicit decay of
its logarithmic-square overhead.

This theorem invokes `sumBound_linear_of_quadraticCostSubdivision` directly.
The old polygon-dependent subdivision tuple is not a premise: the extremal
input, dyadic exponent, raw split, placement, assignment, and tuple are all
chosen internally.  The remaining `overhead_decay` statement is pure
arithmetic and mentions no group, polygon, component, or surgery data. -/
theorem sumBound_linear_of_balancedSurgery_of_overheadDecay
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    (produce : ∀ {n k R : ℕ} (P : SumBoundInput D (b : ℝ) n)
      (B : BalancedSplitData D hsymm b hδ P k R),
        Nonempty (BalancedSplitSurgeryRealization D hsymm b hδ P B))
    (overhead_decay : ∀ R : ℕ, ∃ M : ℕ, ∀ n : ℕ, M < n →
      balancedSurgerySizeOverhead δ R n +
        balancedSurgeryPieceOverhead δ R n ≤
          (1 / 10 : ℝ) * Real.sqrt n) :
    ∃ L : ℕ, ∀ n : ℕ, 1 ≤ n → SumBound D (b : ℝ) n (L * n) := by
  obtain ⟨R, hsplit⟩ := exists_balancedSplitData D hsymm b hδ
  obtain ⟨M, hdecay⟩ := overhead_decay R
  apply sumBound_linear_of_quadraticCostSubdivision D hsymm b hδ
    (balancedSurgeryPieceOverhead δ R)
    (balancedSurgerySizeOverhead δ R) 7 (4 / 5) (1 / 10) M
  · norm_num
  · norm_num
  · norm_num
  · have hsqrt0 := Real.sqrt_nonneg (4 / 5 : ℝ)
    have hsqrt_sq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4 / 5)
    nlinarith
  · exact hdecay
  · intro n hn
    let k := Nat.log 2 n + 1
    have hn8 : 8 ≤ n := by omega
    have hk : n ≤ 2 ^ k := by
      exact le_of_lt (Nat.lt_pow_succ_log_self (b := 2) (by omega) n)
    obtain ⟨childCount, childSides, chordLength, partners, hcount, hchord,
      hcost, hlower, hupper, hsmall, htraversal⟩ :=
      exists_quadraticCostSubdivisionData_of_balancedSurgeryAtRadius
        D hsymm b hδ produce R hsplit hn8 hk
    refine ⟨childCount, childSides, chordLength, partners, ?_, ?_, ?_, ?_,
      ?_, ?_, htraversal⟩
    · have hcount' : childCount ≤
          2 * balancedSurgeryChordCap δ R n + 2 := by
        simpa [balancedSurgeryChordCap, k, Nat.add_assoc] using hcount
      change (childCount : ℝ) ≤ (2 * balancedSurgeryChordCap δ R n + 2 : ℕ)
      exact_mod_cast hcount'
    · exact_mod_cast hcost
    · exact_mod_cast hlower
    · intro h
      exact_mod_cast hupper h
    · have hsquare :
          6 * (chordLength * chordLength) ≤
            6 * ((2 * balancedSurgeryChordCap δ R n + 1) *
              (2 * balancedSurgeryChordCap δ R n + 1)) := by
        have hcap : chordLength ≤ 2 * balancedSurgeryChordCap δ R n + 1 := by
          simpa [balancedSurgeryChordCap, k, Nat.add_assoc] using hchord
        exact Nat.mul_le_mul_left 6 (Nat.mul_le_mul hcap hcap)
      have hsquareR : (↑(6 * (chordLength * chordLength) : ℕ) : ℝ) ≤
          (↑(6 * ((2 * balancedSurgeryChordCap δ R n + 1) *
            (2 * balancedSurgeryChordCap δ R n + 1)) : ℕ) : ℝ) := by
        exact_mod_cast hsquare
      simpa [balancedSurgerySizeOverhead, Nat.cast_mul] using hsquareR
    · intro i
      have hi : (5 : ℝ) * childSides i ≤ 4 * n := by
        exact_mod_cast hsmall i
      nlinarith

end DGOProposition414
end GGT
end GroupApproximation
