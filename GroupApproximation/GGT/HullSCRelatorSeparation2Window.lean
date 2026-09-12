import GroupApproximation.GGT.HullSCRelatorSeparation2Tails
import GroupApproximation.GGT.HullSCRelatorSeparation2Design

/-!
# The design that no window closes against

The greedy construction, with one more finite set avoided at each step: the
powers `GGT/HullSCRelatorSeparation2Tails.lean` collects, so that the new
exponent cannot make an alternating product of bounded length land in the other
subgroup.

The shape of the clause is what makes the induction work.  Exponents are
prepended, so the letters that FOLLOW a given one in the finished relator are
exactly those already chosen when it was picked; the clause is therefore stated
for every splitting `ms = pre ++ n :: post`, and the induction step has only two
cases -- the new exponent, where the choice supplies it, and an old one, where
`post` is unchanged and the hypothesis applies.

Two boundaries are worth naming.  The clause is bounded by the window `W`: only
tails of at most `W` letters are excluded, which is all
`HullSC.notMem_fam_of_crossDeep` leaves open, since osin-ah4's estimate needs the
exclusion only at index-distance at most `1 + b`.  And it ranges over both
indices, for the reason recorded in
`GGT/HullSCRelatorSeparation2Tails.lean`: prepending flips the index of every
exponent already chosen, so the index a letter will carry in the finished
relator is not the one it carries when its exponent is picked.
-/

namespace GroupApproximation
namespace HullSC

universe u

section Window

variable {G : Type u} [Group G]

/-- **The exponent design with the window clause.**

Deep, separated, without repetitions, and: for every splitting of the list, the
exponent at the split makes no product with a bounded tail of what follows it
land in the other subgroup. -/
theorem exists_separated_exponents_window {D : GGT.RelGenSet G Bool}
    (hemb : D.IsHyperbolicallyEmbedded) {a : Bool → G}
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (hfam : ∀ s : Bool, a s ∈ D.fam s) (h₀ h₁ : G) {K : Set G} (hK : K.Finite)
    {T : Set G} (hT : T.Finite) (W L : ℕ) :
    ∃ ms : List ℕ, L ≤ ms.length ∧ ms.Nodup ∧
      (∀ m ∈ ms, ∀ s : Bool, a s ^ m ∉ K ∧ (a s ^ m)⁻¹ ∉ K) ∧
      (∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ s : Bool, ∀ x ∈ T, ∀ x' ∈ T,
        x * a s ^ i * x' ≠ a s ^ j ∧ x * a s ^ i * x' ≠ (a s ^ j)⁻¹) ∧
      ∀ pre post : List ℕ, ∀ n : ℕ, ms = pre ++ n :: post →
        ∀ s t : Bool, ∀ r : ℕ, r ≤ W →
          a s ^ n * GGT.RelLetter.listVal (blockWord h₀ h₁ t (post.take r))
            ∉ D.fam (!s) := by
  induction L with
  | zero =>
      refine ⟨[], Nat.zero_le _, List.nodup_nil, ?_, ?_, ?_⟩
      · intro m hm
        simp at hm
      · intro i hi
        simp at hi
      · intro pre post n h
        cases pre <;> simp at h
  | succ L ih =>
      obtain ⟨ms, hlen, hnodup, hdeep, hsep, hwin⟩ := ih
      obtain ⟨m, hm, hdeepm, hnew⟩ :=
        exists_pow_separated_family hinj hT ms
          (K ∪ windowBadPow D a h₀ h₁ ms W)
          (hK.union (finite_windowBadPow hemb hinj hfam h₀ h₁ ms W))
          (ms.sum + 1)
      have hgt : ∀ j ∈ ms, j < m := by
        intro j hj
        have hle := le_sum_of_mem_nat hj
        omega
      have hnotmem : m ∉ ms := fun hmem => Nat.lt_irrefl m (hgt m hmem)
      have hwinm : ∀ s : Bool, a s ^ m ∉ windowBadPow D a h₀ h₁ ms W := by
        intro s hc
        exact (hdeepm s).1 (Set.mem_union_right _ hc)
      refine ⟨m :: ms, ?_, List.nodup_cons.mpr ⟨hnotmem, hnodup⟩, ?_, ?_, ?_⟩
      · rw [List.length_cons]
        omega
      · intro i hi
        rcases List.mem_cons.mp hi with rfl | hi'
        · intro s
          exact ⟨fun hc => (hdeepm s).1 (Set.mem_union_left _ hc),
            fun hc => (hdeepm s).2 (Set.mem_union_left _ hc)⟩
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
      · intro pre post n hsplit s t r hr
        cases pre with
        | nil =>
            rw [List.nil_append, List.cons.injEq] at hsplit
            obtain ⟨hmn, hmspost⟩ := hsplit
            subst hmn
            subst hmspost
            exact notMem_windowBad_of_notMem hinj hwinm s hr t
        | cons x pre' =>
            rw [List.cons_append, List.cons.injEq] at hsplit
            exact hwin pre' post n hsplit.2 s t r hr

end Window

end HullSC
end GroupApproximation
