import GroupApproximation.GGT.DGOProposition414BalancedSurgery
import GroupApproximation.GGT.DGOAssemblyAdapter
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

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
  chargePlacement : BalancedSplitChargePlacement D hsymm b hδ P B surgery

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
    {n k : ℕ} (hn : 8 ≤ n) (hk : n ≤ 2 ^ k)
    (hquarter : ∀ L a c : ℕ,
      L ≤ 6 * (δ + 6) * (k + 1) + R → c < n →
      n ≤ 4 * (c - a) → 4 * (c - a) ≤ 3 * n →
      5 * ((c - a + 1) + L) ≤ 4 * n ∧
        5 * ((n - c) + a + 1 + L) ≤ 4 * n) :
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
    have hhalf := hquarter B.chord.length B.firstSide B.secondSide
      B.chord_length_le B.secondSide_lt B.quarter_lower B.quarter_upper
    have hfirstSmall : ∀ j,
        5 * ((realization.surgery.intervals.toPathInput).first j).sideCount ≤
          4 * n := by
      intro j
      exact (Nat.mul_le_mul_left 5
        (realization.surgery.first_side_bound j)).trans hhalf.1
    have hsecondSmall : ∀ j,
        5 * ((realization.surgery.intervals.toPathInput).second j).sideCount ≤
          4 * n := by
      intro j
      exact (Nat.mul_le_mul_left 5
        (realization.surgery.second_side_bound j)).trans hhalf.2
    let A := realization.chargePlacement.certificate hfirstSmall hsecondSmall
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

/-- The explicit logarithmic-square overhead of balanced surgery is
eventually smaller than one tenth of the square-root gain. -/
theorem exists_balancedSurgery_overhead_decay (δ R : ℕ) :
    ∃ M : ℕ, ∀ n : ℕ, M < n →
      balancedSurgerySizeOverhead δ R n +
        balancedSurgeryPieceOverhead δ R n ≤
          (1 / 10 : ℝ) * Real.sqrt n := by
  let a : ℕ := 6 * (δ + 6)
  let d : ℕ := 2 * a + R
  let e : ℕ := 2 * d + 1
  let f : ℕ := 2 * d + 2
  let C : ℕ := 6 * ((2 * a + e) * (2 * a + e)) + (2 * a + f)
  let A : ℝ := (C : ℝ) * (2 / Real.log 2) ^ 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA0 : 0 ≤ A := by
    dsimp [A]
    positivity
  have hlittle : (fun x : ℝ => A * Real.log x ^ (2 : ℝ)) =o[Filter.atTop]
      fun x : ℝ => x ^ (1 / 2 : ℝ) :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 2)).const_mul_left A
  obtain ⟨x₀, hx₀⟩ := (Filter.eventually_atTop.1
    (hlittle.bound (by norm_num : (0 : ℝ) < 1 / 10)))
  refine ⟨max 2 (Nat.ceil x₀), ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hx₀n : x₀ ≤ (n : ℝ) := by
    have hceil : x₀ ≤ (Nat.ceil x₀ : ℝ) := Nat.le_ceil x₀
    have hceiln : Nat.ceil x₀ ≤ n := by omega
    exact hceil.trans (by exact_mod_cast hceiln)
  have hasym := hx₀ (n : ℝ) hx₀n
  have hlogn0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  have hrpow0 : 0 ≤ (n : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  rw [Real.norm_of_nonneg
      (mul_nonneg hA0 (Real.rpow_nonneg hlogn0 _)),
    Real.norm_of_nonneg hrpow0] at hasym
  let l : ℕ := Nat.log 2 n
  have hl0 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg _
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
  have he0 : (0 : ℝ) ≤ (e : ℝ) := Nat.cast_nonneg _
  have hf0 : (0 : ℝ) ≤ (f : ℝ) := Nat.cast_nonneg _
  have hcap : (balancedSurgeryChordCap δ R n : ℝ) =
      (a : ℝ) * l + d := by
    simp [balancedSurgeryChordCap, a, d, l]
    ring
  have hq : (2 * balancedSurgeryChordCap δ R n + 1 : ℕ) ≤
      ((2 * a + e : ℕ) : ℝ) * ((l : ℝ) + 1) := by
    push_cast
    rw [hcap]
    have heq : (e : ℝ) = 2 * (d : ℝ) + 1 := by simp [e]
    rw [heq]
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * d + 1) hl0]
  have hp : (2 * balancedSurgeryChordCap δ R n + 2 : ℕ) ≤
      ((2 * a + f : ℕ) : ℝ) * ((l : ℝ) + 1) := by
    push_cast
    rw [hcap]
    have hfeq : (f : ℝ) = 2 * (d : ℝ) + 2 := by simp [f]
    rw [hfeq]
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * d + 2) hl0]
  have hq0 : (0 : ℝ) ≤ (2 * balancedSurgeryChordCap δ R n + 1 : ℕ) := by
    positivity
  have hqSq := mul_self_le_mul_self hq0 hq
  have hl1 : (1 : ℝ) ≤ (l : ℝ) + 1 := by linarith
  have hpSq : (2 * balancedSurgeryChordCap δ R n + 2 : ℕ) ≤
      ((2 * a + f : ℕ) : ℝ) * ((l : ℝ) + 1) ^ 2 := by
    calc
      (2 * balancedSurgeryChordCap δ R n + 2 : ℕ) ≤
          ((2 * a + f : ℕ) : ℝ) * ((l : ℝ) + 1) := hp
      _ ≤ ((2 * a + f : ℕ) : ℝ) * ((l : ℝ) + 1) ^ 2 := by
        apply mul_le_mul_of_nonneg_left
        · nlinarith
        · positivity
  have hover : balancedSurgerySizeOverhead δ R n +
      balancedSurgeryPieceOverhead δ R n ≤
        (C : ℝ) * ((l : ℝ) + 1) ^ 2 := by
    calc
      balancedSurgerySizeOverhead δ R n +
          balancedSurgeryPieceOverhead δ R n =
        6 * (2 * balancedSurgeryChordCap δ R n + 1 : ℕ) ^ 2 +
          (2 * balancedSurgeryChordCap δ R n + 2 : ℕ) := by
            simp [balancedSurgerySizeOverhead, balancedSurgeryPieceOverhead]
            ring
      _ ≤ 6 * (((2 * a + e : ℕ) : ℝ) * ((l : ℝ) + 1)) ^ 2 +
          ((2 * a + f : ℕ) : ℝ) * ((l : ℝ) + 1) ^ 2 := by
            apply add_le_add
            · simpa [pow_two] using
                (mul_le_mul_of_nonneg_left hqSq (by norm_num : (0 : ℝ) ≤ 6))
            · exact hpSq
      _ = (C : ℝ) * ((l : ℝ) + 1) ^ 2 := by
        dsimp [C]
        push_cast
        ring
  have hbridge := DGOPolygonCut.natLog_mul_log_two_le n hn1
  have hlog2n : Real.log 2 ≤ Real.log (n : ℝ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast hn2
  have hl1log : ((l : ℝ) + 1) * Real.log 2 ≤
      2 * Real.log (n : ℝ) := by
    dsimp [l]
    nlinarith
  have hl1bound : (l : ℝ) + 1 ≤
      (2 / Real.log 2) * Real.log (n : ℝ) := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hlog2).2 hl1log
  have hright0 : 0 ≤ (2 / Real.log 2) * Real.log (n : ℝ) := by positivity
  have hsquare := mul_self_le_mul_self (by positivity : 0 ≤ (l : ℝ) + 1) hl1bound
  have hpoly : (C : ℝ) * ((l : ℝ) + 1) ^ 2 ≤
      A * Real.log (n : ℝ) ^ 2 := by
    dsimp [A]
    have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg _
    nlinarith
  calc
    balancedSurgerySizeOverhead δ R n +
        balancedSurgeryPieceOverhead δ R n ≤
      (C : ℝ) * ((l : ℝ) + 1) ^ 2 := hover
    _ ≤ A * Real.log (n : ℝ) ^ 2 := hpoly
    _ = A * Real.log (n : ℝ) ^ (2 : ℝ) := by
      congr 1
      exact (Real.rpow_natCast (Real.log (n : ℝ)) 2).symm
    _ ≤ (1 / 10 : ℝ) * ((n : ℝ) ^ (1 / 2 : ℝ)) := hasym
    _ = (1 / 10 : ℝ) * Real.sqrt n := by
      rw [Real.sqrt_eq_rpow]

/-- Proposition 4.14 from balanced interval surgery and the explicit decay of
its logarithmic-square overhead.

This theorem invokes `sumBound_linear_of_quadraticCostSubdivision` directly.
The old polygon-dependent subdivision tuple is not a premise: the extremal
input, dyadic exponent, raw split, placement, assignment, and tuple are all
chosen internally.  The remaining `overhead_decay` statement is pure
arithmetic and mentions no group, polygon, component, or surgery data. -/
theorem sumBound_linear_of_balancedSurgery
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    (produce : ∀ {n k R : ℕ} (P : SumBoundInput D (b : ℝ) n)
      (B : BalancedSplitData D hsymm b hδ P k R),
        Nonempty (BalancedSplitSurgeryRealization D hsymm b hδ P B)) :
    ∃ L : ℕ, ∀ n : ℕ, 1 ≤ n → SumBound D (b : ℝ) n (L * n) := by
  obtain ⟨R, hsplit⟩ := exists_balancedSplitData D hsymm b hδ
  obtain ⟨M, hdecay⟩ := exists_balancedSurgery_overhead_decay δ R
  let Cq : ℕ := 3 * (6 * (δ + 6)) + R
  obtain ⟨Mq, hquarter⟩ := DGOPolygonCut.exists_quarter_threshold Cq
  let N := max 7 (max Mq 2)
  have hMqN : Mq ≤ N := by simp [N]
  apply sumBound_linear_of_quadraticCostSubdivision D hsymm b hδ
    (balancedSurgeryPieceOverhead δ R)
    (balancedSurgerySizeOverhead δ R) N (4 / 5) (1 / 10) M
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
    have hlogPos : 0 < Nat.log 2 n := by
      by_contra h
      have hlogZero : Nat.log 2 n = 0 := Nat.eq_zero_of_not_pos h
      have hlt := Nat.lt_pow_succ_log_self (b := 2) (by omega) n
      simp [hlogZero] at hlt
      omega
    have hcapLog : balancedSurgeryChordCap δ R n ≤
        Cq * Nat.log 2 n := by
      let a : ℕ := 6 * (δ + 6)
      let l : ℕ := Nat.log 2 n
      have hl : 1 ≤ l := hlogPos
      have hsum : l + 2 ≤ 3 * l := by omega
      calc
        balancedSurgeryChordCap δ R n = a * (l + 2) + R := by
          simp [balancedSurgeryChordCap, a, l]
        _ ≤ a * (3 * l) + R := Nat.add_le_add_right
          (Nat.mul_le_mul_left a hsum) R
        _ ≤ a * (3 * l) + R * l := by
          exact Nat.add_le_add_left (by nlinarith) _
        _ = Cq * l := by dsimp [Cq, a]; ring
        _ = Cq * Nat.log 2 n := rfl
    have hlarge : Mq < n := hMqN.trans_lt hn
    have hquarterAtSplit : ∀ L a c : ℕ,
        L ≤ 6 * (δ + 6) * (k + 1) + R → c < n →
        n ≤ 4 * (c - a) → 4 * (c - a) ≤ 3 * n →
        5 * ((c - a + 1) + L) ≤ 4 * n ∧
          5 * ((n - c) + a + 1 + L) ≤ 4 * n := by
      intro L a c hL hc hlower hupper
      apply hquarter n L a c hlarge
      · apply hL.trans
        simpa [balancedSurgeryChordCap, k, Nat.add_assoc] using hcapLog
      · exact hc
      · exact hlower
      · exact hupper
    obtain ⟨childCount, childSides, chordLength, partners, hcount, hchord,
      hcost, hlower, hupper, hsmall, htraversal⟩ :=
      exists_quadraticCostSubdivisionData_of_balancedSurgeryAtRadius
        D hsymm b hδ produce R hsplit hn8 hk hquarterAtSplit
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
