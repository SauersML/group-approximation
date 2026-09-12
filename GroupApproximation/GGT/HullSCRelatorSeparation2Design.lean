import GroupApproximation.GGT.HullSCRelatorSeparation2Gaps

/-!
# The exponent design over two subgroups

The greedy construction of `GGT/HullSCRelatorSeparationGaps.lean`, run for the
two loxodromic elements of the alternating relator at once.  The only change is
that each step avoids `badSet` for both of them, which is still a finite set, so
the count that made the single-subgroup design free makes this one free too.

The separation is stated per index: a match between two blocks is a match
between blocks of the *same* subgroup, because Osin's components are connected
only within one index, so no cross-subgroup clause is needed and none is
imposed.  Both the direct and the mirrored clause are carried, for `i ≠ j` only
-- at `i = j` the mirrored match is the genuine translation, exactly as over one
subgroup.
-/

namespace GroupApproximation
namespace HullSC

universe u

section Design

variable {G : Type u} [Group G]

/-- **One more exponent, deep for both elements and separated from all those
already chosen.**  The induction is over the list already built, folding the two
`badSet`s of its head into the avoided set before treating the tail. -/
theorem exists_pow_separated_family {a : Bool → G}
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    {T : Set G} (hT : T.Finite) :
    ∀ (js : List ℕ) (K : Set G), K.Finite → ∀ n₀ : ℕ,
      ∃ m : ℕ, n₀ ≤ m ∧ (∀ s : Bool, a s ^ m ∉ K ∧ (a s ^ m)⁻¹ ∉ K) ∧
        ∀ j ∈ js, ∀ s : Bool, ∀ x ∈ T, ∀ x' ∈ T,
          x * a s ^ m * x' ≠ a s ^ j ∧ x * a s ^ j * x' ≠ a s ^ m ∧
            x * a s ^ m * x' ≠ (a s ^ j)⁻¹ ∧
              x * a s ^ j * x' ≠ (a s ^ m)⁻¹ := by
  intro js
  induction js with
  | nil =>
      intro K hK n₀
      obtain ⟨m, hm, hdeep⟩ := exists_deep_pow_family hinj hK n₀
      refine ⟨m, hm, hdeep, ?_⟩
      intro j hj
      simp at hj
  | cons j₀ t ih =>
      intro K hK n₀
      have hfin : (K ∪ badSet (a false) j₀ T ∪ badSet (a true) j₀ T).Finite :=
        (hK.union (finite_badSet _ _ hT)).union (finite_badSet _ _ hT)
      obtain ⟨m, hm, hdeep, hrest⟩ :=
        ih (K ∪ badSet (a false) j₀ T ∪ badSet (a true) j₀ T) hfin n₀
      have hbad : ∀ s : Bool, a s ^ m ∉ badSet (a s) j₀ T ∧
          (a s ^ m)⁻¹ ∉ badSet (a s) j₀ T := by
        intro s
        cases s with
        | false =>
            exact ⟨fun hc => (hdeep false).1
                (Set.mem_union_left _ (Set.mem_union_right _ hc)),
              fun hc => (hdeep false).2
                (Set.mem_union_left _ (Set.mem_union_right _ hc))⟩
        | true =>
            exact ⟨fun hc => (hdeep true).1 (Set.mem_union_right _ hc),
              fun hc => (hdeep true).2 (Set.mem_union_right _ hc)⟩
      refine ⟨m, hm, ?_, ?_⟩
      · intro s
        exact ⟨fun hc => (hdeep s).1
            (Set.mem_union_left _ (Set.mem_union_left _ hc)),
          fun hc => (hdeep s).2
            (Set.mem_union_left _ (Set.mem_union_left _ hc))⟩
      · intro j hj s x hx x' hx'
        rcases List.mem_cons.mp hj with hje | hj'
        · rw [hje]
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro hc
            refine (hbad s).1 ?_
            have heq : x⁻¹ * a s ^ j₀ * x'⁻¹ = a s ^ m := by
              rw [← hc, mul_assoc x (a s ^ m) x', inv_mul_cancel_left,
                mul_inv_cancel_right]
            exact heq ▸ mem_badSet_of_left hx hx'
          · intro hc
            exact (hbad s).1 (hc ▸ mem_badSet_of_mid hx hx')
          · intro hc
            refine (hbad s).1 ?_
            have heq : x⁻¹ * (a s ^ j₀)⁻¹ * x'⁻¹ = a s ^ m := by
              rw [← hc, mul_assoc x (a s ^ m) x', inv_mul_cancel_left,
                mul_inv_cancel_right]
            exact heq ▸ mem_badSet_of_right hx hx'
          · intro hc
            exact (hbad s).2 (hc ▸ mem_badSet_of_mid hx hx')
        · exact hrest j hj' s x hx x' hx'

/-- **Arbitrarily long lists of exponents, deep and separated for both
elements.**  As over one subgroup: the exponents are added one at a time, each
past the sum of those already chosen, which keeps the list without
repetitions. -/
theorem exists_separated_exponents_family {a : Bool → G}
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    {K : Set G} (hK : K.Finite) {T : Set G} (hT : T.Finite) (L : ℕ) :
    ∃ ms : List ℕ, L ≤ ms.length ∧ ms.Nodup ∧
      (∀ m ∈ ms, ∀ s : Bool, a s ^ m ∉ K ∧ (a s ^ m)⁻¹ ∉ K) ∧
      ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ s : Bool, ∀ x ∈ T, ∀ x' ∈ T,
        x * a s ^ i * x' ≠ a s ^ j ∧ x * a s ^ i * x' ≠ (a s ^ j)⁻¹ := by
  induction L with
  | zero =>
      refine ⟨[], Nat.zero_le _, List.nodup_nil, ?_, ?_⟩
      · intro m hm
        simp at hm
      · intro i hi
        simp at hi
  | succ L ih =>
      obtain ⟨ms, hlen, hnodup, hdeep, hsep⟩ := ih
      obtain ⟨m, hm, hdeepm, hnew⟩ :=
        exists_pow_separated_family hinj hT ms K hK (ms.sum + 1)
      have hnotmem : m ∉ ms := by
        intro hmem
        have hle : m ≤ ms.sum := le_sum_of_mem_nat hmem
        omega
      refine ⟨m :: ms, ?_, List.nodup_cons.mpr ⟨hnotmem, hnodup⟩, ?_, ?_⟩
      · rw [List.length_cons]
        omega
      · intro i hi
        rcases List.mem_cons.mp hi with rfl | hi'
        · exact hdeepm
        · exact hdeep i hi'
      · intro i hi j hj hij s x hx x' hx'
        rcases List.mem_cons.mp hi with rfl | hi'
        · rcases List.mem_cons.mp hj with rfl | hj'
          · exact absurd rfl hij
          · exact ⟨(hnew j hj' s x hx x' hx').1,
              (hnew j hj' s x hx x' hx').2.2.1⟩
        · rcases List.mem_cons.mp hj with rfl | hj'
          · exact ⟨(hnew i hi' s x hx x' hx').2.1,
              (hnew i hi' s x hx x' hx').2.2.2⟩
          · exact hsep i hi' j hj' hij s x hx x' hx'

end Design

end HullSC
end GroupApproximation
