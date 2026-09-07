import GroupApproximation.GGT.DGOProposition414GeneralSubdivision

/-!
# The uniform linear DGO sum bound at general parameters

The general least-cost function satisfies the proved subdivision inequality.
The logarithmic-square overhead and fixed child-size contraction are exactly
those in the additive case; the numerical linearity theorem applies unchanged.
-/

namespace GroupApproximation.GGT.DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w
variable {G : Type u} [Group G] {Λ : Type w}

/-- One linear sum bound works for every polygon size and every input at the
fixed genuine general quasi-geodesic parameters. -/
theorem quasiSumBound_linear
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (mu : ℝ) (b : ℕ)
    (hmu : 1 ≤ mu)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) :
    ∃ L : ℕ, ∀ n : ℕ, 1 ≤ n → QuasiSumBound D mu (b : ℝ) n (L * n) := by
  obtain ⟨R, hsplit⟩ := QuasiSumBoundInput.exists_balancedSplitData_quasi
    D hsymm mu (b : ℝ) hmu (Nat.cast_nonneg b) hδ
  obtain ⟨M, hdecay⟩ := exists_balancedSurgery_overhead_decay δ R
  let Cq : ℕ := 3 * (6 * (δ + 6)) + R
  obtain ⟨Mq, hquarter⟩ := DGOPolygonCut.exists_quarter_threshold Cq
  let N := max 7 (max Mq 2)
  have hMqN : Mq ≤ N := by simp [N]
  have hH : ∀ n : ℕ, N < n → ∃ (childCount : ℕ) (childSides : Fin childCount → ℕ),
      (childCount : ℝ) ≤ balancedSurgeryPieceOverhead δ R n ∧
      (quasiSumCost D hsymm mu b hmu hδ n : ℝ) ≤
        ∑ i, (quasiSumCost D hsymm mu b hmu hδ (childSides i) : ℝ) ∧
      (n : ℝ) ≤ ∑ i, (childSides i : ℝ) ∧
      (∑ i, (childSides i : ℝ)) ≤ (n : ℝ) + balancedSurgerySizeOverhead δ R n ∧
      ∀ i, (childSides i : ℝ) ≤ (4 / 5 : ℝ) * n := by
    intro n hn
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
    obtain ⟨childCount, childSides, hcount, hcost, hlower, hupper, hsmall⟩ :=
      exists_quasiCostSubdivisionData_atRadius D hsymm mu b hmu hδ R hsplit
        hn8 hk hquarterAtSplit
    refine ⟨childCount, childSides, ?_, ?_, ?_, ?_, ?_⟩
    · have hcount' : childCount ≤ 2 * balancedSurgeryChordCap δ R n + 2 := by
        simpa [balancedSurgeryChordCap, k, Nat.add_assoc] using hcount
      change (childCount : ℝ) ≤ (2 * balancedSurgeryChordCap δ R n + 2 : ℕ)
      exact_mod_cast hcount'
    · exact_mod_cast hcost
    · exact_mod_cast hlower
    · have hupper' : (∑ i, childSides i) ≤ n +
          6 * ((2 * balancedSurgeryChordCap δ R n + 1) *
            (2 * balancedSurgeryChordCap δ R n + 1)) := by
        simpa [balancedSurgeryChordCap, k, Nat.add_assoc, pow_two] using hupper
      have hupperR := Nat.cast_le (α := ℝ).mpr hupper'
      simpa [balancedSurgerySizeOverhead] using hupperR
    · intro i
      have hi : (5 : ℝ) * childSides i ≤ 4 * n := by exact_mod_cast hsmall i
      nlinarith
  have hgain : Real.sqrt (4 / 5 : ℝ) * (1 + 1 / 10) ≤ 1 := by
    have hsqrt0 := Real.sqrt_nonneg (4 / 5 : ℝ)
    have hsqrt_sq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4 / 5)
    nlinarith
  obtain ⟨L, hlinear⟩ := DGO.nat_linear_of_subdivision_of_sqrt_overhead
    (quasiSumCost D hsymm mu b hmu hδ)
    (balancedSurgeryPieceOverhead δ R) (balancedSurgerySizeOverhead δ R)
    N (4 / 5) (1 / 10) M (by norm_num) (by norm_num) (by norm_num)
    hgain hdecay hH
  exact ⟨L, fun n hn =>
    (quasiSumBound_quasiSumCost D hsymm mu b hmu hδ n).mono (hlinear n hn)⟩

/-- Positive-radius form in the original general uniform-sum interface. -/
theorem exists_uniformSumBound_general
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (mu : ℝ) (b : ℕ)
    (hmu : 1 ≤ mu)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) :
    ∃ C : ℕ, 0 < C ∧ DGOUniformSumBound D mu (b : ℝ) C := by
  obtain ⟨L, hL⟩ := quasiSumBound_linear D hsymm mu b hmu hδ
  refine ⟨L + 1, by omega, ?_⟩
  intro n v word cut I lam hlet hclosed hcut hI hedge hcomp hiso hquasi
  by_cases hn : n = 0
  · subst n
    have hIempty : I = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro s hs
      have hlt := hI s hs
      omega)
    exact ⟨fun _ => 0, by simp [hIempty], by simp [hIempty]⟩
  · let P : QuasiSumBoundInput D mu (b : ℝ) n :=
      ⟨v, word, cut, I, lam, hlet, hclosed, hcut, hI, hedge, hcomp, hiso, hquasi⟩
    obtain ⟨r, hr, hsum⟩ := hL n (by omega) P
    exact ⟨r, hr, hsum.trans (Nat.mul_le_mul_right n (by omega))⟩

end GroupApproximation.GGT.DGOProposition414

#audit_axioms GroupApproximation.GGT.DGOProposition414.quasiSumBound_linear
#audit_axioms GroupApproximation.GGT.DGOProposition414.exists_uniformSumBound_general
