import GroupApproximation.GGT.HullSCRelatorSeparation2Cross

/-!
# Deep differences

The design makes each exponent deep.  The windowed same-side exclusion needs
more: that the **differences** of exponents are deep too.  The reason is the
pinning argument.  An alternating product of block letters lying in `H_λ` is,
after stripping its first letter, a product whose leftmost exponent is the
newest one chosen; if two exponents could both stand there against the same
older tail, their difference would be a power of one element lying in the other
subgroup, and `HullSC.notMem_fam_of_crossDeep` forbids exactly that -- for a
*deep* power.  So the differences have to be deep, and this module arranges it.

The arrangement costs one more finite set at each greedy step, and the encoding
is what keeps it inside the existing machinery: `a_s^{m-j} ∈ B` is
`a_s^m ∈ a_s^j · B`, a translate of a finite set.  So "the difference with an
exponent already chosen is shallow" is again a condition on `a_s^m` lying in a
finite set of group elements, which is what the greedy step already avoids.

`diffBad` is that set of translates, over the exponents chosen so far and both
elements; `exists_separated_exponents_diff` is the design carrying the extra
clause.  Nothing else changes: the deep clause and the separation clause are
produced exactly as in `GGT/HullSCRelatorSeparation2Design.lean`.
-/

namespace GroupApproximation
namespace HullSC

universe u

section Diff

variable {G : Type u} [Group G]

/-- **The translates a new exponent must miss** for its differences with the
exponents already chosen to be deep. -/
def diffBad (a : Bool → G) (B : Set G) (js : List ℕ) : Set G :=
  ⋃ j ∈ {j : ℕ | j ∈ js},
    ((fun g => a false ^ j * g) '' B ∪ (fun g => a true ^ j * g) '' B)

theorem finite_diffBad (a : Bool → G) {B : Set G} (hB : B.Finite)
    (js : List ℕ) : (diffBad a B js).Finite :=
  (List.finite_toSet js).biUnion fun _ _ => (hB.image _).union (hB.image _)

/-- **Missing the translates is having deep differences.** -/
theorem notMem_of_notMem_diffBad {a : Bool → G} {B : Set G} {js : List ℕ}
    {m : ℕ} (h : ∀ s : Bool, a s ^ m ∉ diffBad a B js) {j : ℕ} (hj : j ∈ js)
    (hjm : j ≤ m) (s : Bool) : a s ^ (m - j) ∉ B := by
  intro hmem
  refine h s ?_
  refine Set.mem_biUnion (show j ∈ {j : ℕ | j ∈ js} from hj) ?_
  cases s with
  | false =>
      refine Set.mem_union_left _ ⟨a false ^ (m - j), hmem, ?_⟩
      show a false ^ j * a false ^ (m - j) = a false ^ m
      rw [← pow_add, show j + (m - j) = m from by omega]
  | true =>
      refine Set.mem_union_right _ ⟨a true ^ (m - j), hmem, ?_⟩
      show a true ^ j * a true ^ (m - j) = a true ^ m
      rw [← pow_add, show j + (m - j) = m from by omega]

/-- **The design with deep differences.**

The three clauses of `HullSC.exists_separated_exponents_family`, and a fourth:
the difference of any two exponents is deep as well.  The greedy step avoids one
more finite set, the translates of the depth ball by the powers already
chosen. -/
theorem exists_separated_exponents_diff {a : Bool → G}
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    {K : Set G} (hK : K.Finite) {T : Set G} (hT : T.Finite)
    {B : Set G} (hB : B.Finite) (L : ℕ) :
    ∃ ms : List ℕ, L ≤ ms.length ∧ ms.Nodup ∧
      (∀ m ∈ ms, ∀ s : Bool, a s ^ m ∉ K ∧ (a s ^ m)⁻¹ ∉ K) ∧
      (∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ s : Bool, ∀ x ∈ T, ∀ x' ∈ T,
        x * a s ^ i * x' ≠ a s ^ j ∧ x * a s ^ i * x' ≠ (a s ^ j)⁻¹) ∧
      ∀ i ∈ ms, ∀ j ∈ ms, j < i → ∀ s : Bool, a s ^ (i - j) ∉ B := by
  induction L with
  | zero =>
      refine ⟨[], Nat.zero_le _, List.nodup_nil, ?_, ?_, ?_⟩
      · intro m hm
        simp at hm
      · intro i hi
        simp at hi
      · intro i hi
        simp at hi
  | succ L ih =>
      obtain ⟨ms, hlen, hnodup, hdeep, hsep, hdiff⟩ := ih
      obtain ⟨m, hm, hdeepm, hnew⟩ :=
        exists_pow_separated_family hinj hT ms (K ∪ diffBad a B ms)
          (hK.union (finite_diffBad a hB ms)) (ms.sum + 1)
      have hgt : ∀ j ∈ ms, j < m := by
        intro j hj
        have hle := le_sum_of_mem_nat hj
        omega
      have hnotmem : m ∉ ms := fun hmem => Nat.lt_irrefl m (hgt m hmem)
      have hdiffm : ∀ s : Bool, a s ^ m ∉ diffBad a B ms := by
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
      · intro i hi j hj hji s
        rcases List.mem_cons.mp hi with rfl | hi'
        · have hjms : j ∈ ms := by
            rcases List.mem_cons.mp hj with rfl | hj'
            · exfalso
              omega
            · exact hj'
          exact notMem_of_notMem_diffBad hdiffm hjms (le_of_lt (hgt j hjms)) s
        · have hjms : j ∈ ms := by
            rcases List.mem_cons.mp hj with rfl | hj'
            · exfalso
              have hlt := hgt i hi'
              omega
            · exact hj'
          exact hdiff i hi' j hjms hji s

end Diff

end HullSC
end GroupApproximation
