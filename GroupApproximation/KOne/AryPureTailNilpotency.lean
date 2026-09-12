import GroupApproximation.KOne.AryGradedComponents
import GroupApproximation.KOne.AryWindowProductClosure
import GroupApproximation.Meta.AxiomGuard

/-!
# Pure tails of units are nilpotent, at arbitrary arity

`KOne/PureTailNilpotency.lean` for `L_k(1,d)`: if `1 + η` is a unit with `η` of pure
degree `1`, then `η` is nilpotent.  Decomposing the inverse into graded components, the
equation `(1 + η)·u⁻¹ = 1` reads degreewise as a two-term recursion whose negative
components vanish from the bottom up, whose zero component is `1`, and whose positive
components are `(-η)^j`; finiteness of the inverse's window then forces a power of `η`
to vanish.  The argument uses only the graded structure, so the arity enters only
through `AryLeavitt.components_unique`.
-/

namespace GroupApproximation
namespace AryLeavitt

open CompleteMatrixFamily

variable (k : Type) [Field k] (d : ℕ)

/-- **Pure tails of units are nilpotent.** -/
theorem pure_tail_nilpotent (hd : 2 ≤ d) {η : AryLeavittAlgebra k d}
    (hη : η ∈ Submodule.span k ((family k d).degreeMonomials 1 1))
    (u : (AryLeavittAlgebra k d)ˣ)
    (hu : (u : AryLeavittAlgebra k d) = 1 + η) :
    ∃ D : ℕ, η ^ D = 0 := by
  classical
  obtain ⟨lo₀, hi₀, hx₀⟩ := exists_mem_span_degreeMonomials k d
    ((u⁻¹ : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d)
  set lo : ℤ := min lo₀ (-1) with hlo
  set hi : ℤ := max hi₀ 0 with hhi
  have hlo1 : lo ≤ -1 := min_le_right _ _
  have hlo2 : lo ≤ lo₀ := min_le_left _ _
  have hhi1 : (0 : ℤ) ≤ hi := le_max_right _ _
  have hhi2 : hi₀ ≤ hi := le_max_left _ _
  have hx : ((u⁻¹ : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) ∈
      Submodule.span k ((family k d).degreeMonomials lo hi) :=
    (family k d).span_degreeMonomials_mono hlo2 hhi2 hx₀
  obtain ⟨y, hymem, hysupp, hysum⟩ := (family k d).exists_components hx
  set D : Finset ℤ := Finset.Icc lo (hi + 1) with hD
  have h0D : (0 : ℤ) ∈ D := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  -- component membership of the two decompositions of `1`
  have hzmem : ∀ j ∈ D, y j + η * y (j - 1) ∈
      Submodule.span k ((family k d).degreeMonomials j j) := by
    intro j _
    refine Submodule.add_mem _ (hymem j) ?_
    have := (family k d).window_mul_mem_span (k := k) hη (hymem (j - 1))
    refine (family k d).span_degreeMonomials_mono ?_ ?_ this <;> omega
  have hz'mem : ∀ j ∈ D,
      (if j = 0 then (1 : AryLeavittAlgebra k d) else 0) ∈
      Submodule.span k ((family k d).degreeMonomials j j) := by
    intro j _
    by_cases hj : j = 0
    · rw [if_pos hj]
      exact Submodule.subset_span ⟨[], [], by simp [hj], by simp [hj], by simp⟩
    · rw [if_neg hj]
      exact Submodule.zero_mem _
  -- the shifted sum
  have hshift : ∑ j ∈ D, y (j - 1) =
      ((u⁻¹ : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) := by
    have hmap : D = Finset.map (addRightEmbedding (1 : ℤ))
        (Finset.Icc (lo - 1) hi) := by
      rw [Finset.map_add_right_Icc, show lo - 1 + 1 = lo from by ring]
    rw [hmap, Finset.sum_map]
    have hstep : ∀ j ∈ Finset.Icc (lo - 1) hi,
        y (addRightEmbedding (1 : ℤ) j - 1) = y j := by
      intro j _
      congr 1
      simp [addRightEmbedding]
    rw [Finset.sum_congr rfl hstep]
    have hins : Finset.Icc (lo - 1) hi = insert (lo - 1) (Finset.Icc lo hi) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hins, Finset.sum_insert (by
        simp only [Finset.mem_Icc]
        omega),
      hysupp (lo - 1) (Or.inl (by omega)), zero_add, hysum]
  -- the plain sum
  have hplain : ∑ j ∈ D, y j =
      ((u⁻¹ : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) := by
    have hins : D = insert (hi + 1) (Finset.Icc lo hi) := by
      ext j
      simp only [hD, Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hins, Finset.sum_insert (by
        simp only [Finset.mem_Icc]
        omega),
      hysupp (hi + 1) (Or.inr (by omega)), zero_add, hysum]
  -- both decompositions sum to `1`
  have hsum1 : ∑ j ∈ D, (y j + η * y (j - 1)) = 1 := by
    rw [Finset.sum_add_distrib, hplain, ← Finset.mul_sum, hshift]
    calc ((u⁻¹ : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) +
          η * ((u⁻¹ : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d)
        = (1 + η) * ((u⁻¹ : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) := by
          noncomm_ring
      _ = (u : AryLeavittAlgebra k d) *
          ((u⁻¹ : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) := by rw [hu]
      _ = 1 := u.mul_inv
  have hsum2 : ∑ j ∈ D, (if j = 0 then (1 : AryLeavittAlgebra k d) else 0) = 1 := by
    rw [Finset.sum_ite_eq' D (0 : ℤ) (fun _ ↦ (1 : AryLeavittAlgebra k d)), if_pos h0D]
  -- componentwise equations
  have heq := components_unique k d hd hzmem hz'mem (hsum1.trans hsum2.symm)
  -- negative components vanish, from the bottom up
  have hnegstep : ∀ n : ℕ, ∀ j : ℤ, j = lo + n → j < 0 → y j = 0 := by
    intro n
    induction n with
    | zero =>
        intro j hj _
        have hmem : j ∈ D := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        have h := heq j hmem
        rw [if_neg (by omega), hysupp (j - 1) (Or.inl (by omega)), mul_zero,
          add_zero] at h
        exact h
    | succ m ih =>
        intro j hj hjneg
        have hprev : y (j - 1) = 0 := ih (j - 1) (by omega) (by omega)
        have hmem : j ∈ D := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        have h := heq j hmem
        rw [if_neg (by omega), hprev, mul_zero, add_zero] at h
        exact h
  have hneg : ∀ j : ℤ, j < 0 → y j = 0 := by
    intro j hj
    by_cases h : j < lo
    · exact hysupp j (Or.inl h)
    · exact hnegstep (j - lo).toNat j (by omega) hj
  -- the zero component is `1`
  have h0 : y 0 = 1 := by
    have h := heq 0 h0D
    rw [if_pos rfl, hneg (0 - 1) (by omega), mul_zero, add_zero] at h
    exact h
  -- positive components form the geometric sequence
  have hpos : ∀ n : ℕ, (n : ℤ) ≤ hi + 1 → y (n : ℤ) = (-η) ^ n := by
    intro n
    induction n with
    | zero =>
        intro _
        simpa using h0
    | succ m ih =>
        intro hle
        have hcast : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
        have hmem : ((m : ℤ) + 1) ∈ D := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        have h := heq ((m : ℤ) + 1) hmem
        rw [if_neg (by omega), show (m : ℤ) + 1 - 1 = (m : ℤ) from by ring,
          ih (by omega)] at h
        have hval : y ((m : ℤ) + 1) = -(η * (-η) ^ m) := add_eq_zero_iff_eq_neg.mp h
        rw [hcast, hval, pow_succ']
        exact (neg_mul η ((-η) ^ m)).symm
  -- the top equation kills the geometric sequence
  have hhiD : (hi + 1) ∈ D := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have htop := heq (hi + 1) hhiD
  rw [if_neg (by omega), hysupp (hi + 1) (Or.inr (by omega)), zero_add,
    show hi + 1 - 1 = hi from by ring] at htop
  have hyhi : y hi = (-η) ^ hi.toNat := by
    have := hpos hi.toNat (by omega)
    rwa [Int.toNat_of_nonneg hhi1] at this
  rw [hyhi] at htop
  refine ⟨hi.toNat + 1, ?_⟩
  rcases Nat.even_or_odd hi.toNat with he | ho
  · rw [Even.neg_pow he η] at htop
    rw [pow_succ']
    exact htop
  · rw [Odd.neg_pow ho η, mul_neg, neg_eq_zero] at htop
    rw [pow_succ']
    exact htop

end AryLeavitt
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.AryLeavitt.pure_tail_nilpotent
