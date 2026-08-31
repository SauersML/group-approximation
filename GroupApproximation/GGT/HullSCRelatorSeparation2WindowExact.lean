import GroupApproximation.GGT.HullSCRelatorSeparation2Window
import GroupApproximation.GGT.DGOProposition433Finite

/-!
# The windowed exponent design at an exact length

`HullSC.exists_separated_exponents_window` states only a lower bound on the
length it constructs.  Its recursion in fact adds exactly one exponent at each
step.  The exact form matters when the depth radius is chosen from the length
of the eventual relator: it removes an otherwise circular dependence between
the radius and the list returned by the construction.
-/

namespace GroupApproximation
namespace HullSC

universe u

section WindowExact

variable {G : Type u} [Group G]

/-- **Only finitely many powers can close a fixed two-sided context into a
peripheral subgroup.**

This is the form needed by a greedy construction when the unique base letter
lies between two block arcs.  Two successful exponents cancel the fixed right
context; their quotient is a conjugate by the fixed left context, and DGO
Proposition 4.33 makes the possible differences finite. -/
theorem finite_mul_pow_mul_mem_fam {D : GGT.RelGenSet G Bool}
    (hemb : D.IsHyperbolicallyEmbedded) {lam mu : Bool} {a A B : G}
    (hmid : ¬ (lam = mu ∧ A ∈ D.fam mu))
    (hinj : Function.Injective (fun n : ℕ => a ^ n))
    (hmem : ∀ n : ℕ, a ^ n ∈ D.fam lam) :
    {n : ℕ | A * a ^ n * B ∈ D.fam mu}.Finite := by
  have hfin : {d : ℕ | A * a ^ d * A⁻¹ ∈ D.fam mu}.Finite :=
    GGT.finite_conj_pow_mem_fam D hemb hmid hinj hmem
  rcases Set.eq_empty_or_nonempty {n : ℕ | A * a ^ n * B ∈ D.fam mu} with
    hemp | ⟨n₀, hn₀⟩
  · rw [hemp]
    exact Set.finite_empty
  · refine Set.Finite.subset
      ((Set.finite_Iio n₀).union (hfin.image (fun d => n₀ + d))) ?_
    intro n hn
    rcases Nat.lt_or_ge n n₀ with hlt | hge
    · exact Set.mem_union_left _ hlt
    · refine Set.mem_union_right _ ?_
      have hadd : n₀ + (n - n₀) = n := Nat.add_sub_of_le hge
      have himage : n₀ + (n - n₀) ∈
          (fun d ↦ n₀ + d) '' {d : ℕ | A * a ^ d * A⁻¹ ∈ D.fam mu} := by
        refine ⟨n - n₀, ?_, rfl⟩
        show A * a ^ (n - n₀) * A⁻¹ ∈ D.fam mu
        have hprod :
            (A * a ^ n * B) * (A * a ^ n₀ * B)⁻¹ =
              A * a ^ (n - n₀) * A⁻¹ := by
          rw [mul_inv_rev, mul_inv_rev]
          rw [show a ^ n = a ^ (n - n₀) * a ^ n₀ by
            rw [← pow_add, show n - n₀ + n₀ = n by omega]]
          group
        have hmul :
            (A * a ^ n * B) * (A * a ^ n₀ * B)⁻¹ ∈ D.fam mu :=
          mul_mem hn (inv_mem hn₀)
        rw [hprod] at hmul
        exact hmul
      exact hadd ▸ himage

/-- **The windowed exponent design has exactly the requested length.** -/
theorem exists_separated_exponents_window_exact {D : GGT.RelGenSet G Bool}
    (hemb : D.IsHyperbolicallyEmbedded) {a : Bool → G}
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (hfam : ∀ s : Bool, a s ∈ D.fam s) (h₀ h₁ : G) {K : Set G} (hK : K.Finite)
    {T : Set G} (hT : T.Finite) (W L : ℕ) :
    ∃ ms : List ℕ, ms.length = L ∧ ms.Nodup ∧
      (∀ m ∈ ms, ∀ s : Bool, a s ^ m ∉ K ∧ (a s ^ m)⁻¹ ∉ K) ∧
      (∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ s : Bool, ∀ x ∈ T, ∀ x' ∈ T,
        x * a s ^ i * x' ≠ a s ^ j ∧ x * a s ^ i * x' ≠ (a s ^ j)⁻¹) ∧
      ∀ pre post : List ℕ, ∀ n : ℕ, ms = pre ++ n :: post →
        ∀ s t : Bool, ∀ r : ℕ, r ≤ W →
          a s ^ n * GGT.RelLetter.listVal (blockWord h₀ h₁ t (post.take r))
            ∉ D.fam (!s) := by
  induction L with
  | zero =>
      refine ⟨[], rfl, List.nodup_nil, ?_, ?_, ?_⟩
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
      refine ⟨m :: ms, by simp [hlen], List.nodup_cons.mpr ⟨hnotmem, hnodup⟩,
        ?_, ?_, ?_⟩
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

end WindowExact

end HullSC
end GroupApproximation
