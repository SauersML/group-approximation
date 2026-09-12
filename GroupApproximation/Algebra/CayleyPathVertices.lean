import GroupApproximation.Algebra.LinearStokesQuadrangle

/-!
# Vertices of paths in a Cayley graph

`DiscreteStokes.listPoints b l` lists the vertices visited when the word `l` of
group elements is read from `b`.  This module records the facts about those
vertices that the proof of Gromov's theorem uses: every vertex is `b` times the
product of an initial segment; the vertices of a concatenation are those of the two
pieces; reading the formally inverse word backwards from the endpoint visits the
same vertices; the vertices of a word lie within its length of either endpoint; and
the vertices of a geodesic word are at their index distance from each other, a
middle segment visiting only vertices of the whole.
-/

namespace GroupApproximation
namespace DiscreteStokes

open WordMetric

universe v

variable {Q : Type v} [Group Q]

/-! ## Membership -/

/-- Every vertex is the start times the product of an initial segment, and every
such product is a vertex. -/
theorem mem_listPoints_iff (b : Q) (l : List Q) (q : Q) :
    q ∈ listPoints b l ↔ ∃ i : ℕ, q = b * (l.take i).prod := by
  induction l generalizing b with
  | nil =>
      simp only [listPoints_nil, List.mem_singleton, List.take_nil, List.prod_nil, mul_one]
      exact ⟨fun h => ⟨0, h⟩, fun ⟨_, h⟩ => h⟩
  | cons x l ih =>
      rw [listPoints_cons, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨i, rfl⟩)
        · exact ⟨0, by simp⟩
        · exact ⟨i + 1, by simp [mul_assoc]⟩
      · rintro ⟨i, rfl⟩
        cases i with
        | zero => exact Or.inl (by simp)
        | succ i => exact Or.inr ⟨i, by simp [mul_assoc]⟩

/-- The index of a vertex can be taken at most the length. -/
theorem exists_index_of_mem_listPoints {b : Q} {l : List Q} {q : Q} (hq : q ∈ listPoints b l) :
    ∃ i : ℕ, i ≤ l.length ∧ q = b * (l.take i).prod := by
  obtain ⟨i, rfl⟩ := (mem_listPoints_iff b l q).mp hq
  by_cases hi : i ≤ l.length
  · exact ⟨i, hi, rfl⟩
  · refine ⟨l.length, le_rfl, ?_⟩
    rw [List.take_of_length_le (by omega), List.take_length]

theorem start_mem_listPoints (b : Q) (l : List Q) : b ∈ listPoints b l :=
  (mem_listPoints_iff b l b).mpr ⟨0, by simp⟩

theorem end_mem_listPoints (b : Q) (l : List Q) : b * l.prod ∈ listPoints b l :=
  (mem_listPoints_iff b l _).mpr ⟨l.length, by rw [List.take_length]⟩

/-- The vertices of a concatenation are those of the two pieces. -/
theorem mem_listPoints_append (b : Q) (l m : List Q) (q : Q) :
    q ∈ listPoints b (l ++ m) ↔ q ∈ listPoints b l ∨ q ∈ listPoints (b * l.prod) m := by
  induction l generalizing b with
  | nil =>
      simp only [List.nil_append, listPoints_nil, List.mem_singleton, List.prod_nil, mul_one]
      constructor
      · exact Or.inr
      · rintro (rfl | h)
        · exact start_mem_listPoints _ _
        · exact h
  | cons x l ih =>
      simp only [List.cons_append, listPoints_cons, List.mem_cons, ih, List.prod_cons,
        mul_assoc, or_assoc]

/-! ## Reversal -/

/-- The formally inverse word, read backwards. -/
def revList (l : List Q) : List Q :=
  (l.map fun x => x⁻¹).reverse

@[simp] theorem revList_nil : revList ([] : List Q) = [] := rfl

theorem revList_cons (x : Q) (l : List Q) : revList (x :: l) = revList l ++ [x⁻¹] := by
  simp [revList]

theorem prod_revList (l : List Q) : (revList l).prod = l.prod⁻¹ :=
  (List.prod_inv_reverse l).symm

@[simp] theorem length_revList (l : List Q) : (revList l).length = l.length := by
  simp [revList]

theorem letters_revList {S : Set Q} (hS : IsSymmetricGeneratingSet S) {l : List Q}
    (hl : ∀ x ∈ l, x ∈ S) : ∀ x ∈ revList l, x ∈ S := by
  intro x hx
  simp only [revList, List.mem_reverse, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact hS.inv_mem y (hl y hy)

/-- Appending one letter appends one vertex. -/
theorem listPoints_append_singleton (c : Q) (m : List Q) (y : Q) :
    listPoints c (m ++ [y]) = listPoints c m ++ [c * m.prod * y] := by
  induction m generalizing c with
  | nil => simp
  | cons z m ih => simp only [List.cons_append, listPoints_cons, ih, List.prod_cons, mul_assoc]

/-- **Reading the inverse word backwards from the endpoint visits the same
vertices.** -/
theorem mem_listPoints_revList (b : Q) (l : List Q) (q : Q) :
    q ∈ listPoints (b * l.prod) (revList l) ↔ q ∈ listPoints b l := by
  induction l generalizing b with
  | nil => simp
  | cons x l ih =>
      have e : b * (x :: l).prod * (revList l).prod * x⁻¹ = b := by
        rw [prod_revList, List.prod_cons]
        group
      rw [revList_cons, listPoints_append_singleton, e, List.prod_cons, ← mul_assoc,
        List.mem_append, ih (b * x), listPoints_cons, List.mem_cons, List.mem_singleton]
      exact or_comm

/-! ## Distances from the endpoints -/

/-- A vertex of a word is within the length of the start. -/
theorem wordDist_start_le_of_mem {S : Set Q} {b : Q} {l : List Q} (hl : ∀ x ∈ l, x ∈ S)
    {q : Q} (hq : q ∈ listPoints b l) : wordDist S b q ≤ l.length := by
  obtain ⟨i, _, rfl⟩ := exists_index_of_mem_listPoints hq
  unfold wordDist
  rw [inv_mul_cancel_left]
  calc wordNorm S (l.take i).prod ≤ (l.take i).length :=
        wordNorm_le_length ⟨fun x hx => hl x (List.mem_of_mem_take hx), rfl⟩
    _ ≤ l.length := List.length_take_le' _ _

/-- A vertex of a word is within the length of the endpoint. -/
theorem wordDist_end_le_of_mem {S : Set Q} {b : Q} {l : List Q} (hl : ∀ x ∈ l, x ∈ S)
    {q : Q} (hq : q ∈ listPoints b l) : wordDist S q (b * l.prod) ≤ l.length := by
  obtain ⟨i, _, rfl⟩ := exists_index_of_mem_listPoints hq
  unfold wordDist
  have e : (b * (l.take i).prod)⁻¹ * (b * l.prod) = (l.drop i).prod := by
    rw [← List.prod_take_mul_prod_drop l i]
    group
  rw [e]
  calc wordNorm S (l.drop i).prod ≤ (l.drop i).length :=
        wordNorm_le_length ⟨fun x hx => hl x (List.mem_of_mem_drop hx), rfl⟩
    _ ≤ l.length := by rw [List.length_drop]; exact Nat.sub_le _ _

/-! ## Geodesic words -/

/-- **Vertices of a geodesic word are at their index distance.** -/
theorem wordDist_take_of_geodesic {S : Set Q} (hS : IsSymmetricGeneratingSet S)
    {γ : List Q} (hγ : IsGeodesicWord S γ γ.prod) (A : Q) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ γ.length) :
    wordDist S (A * (γ.take i).prod) (A * (γ.take j).prod) = j - i := by
  have hsplit : γ.take j = γ.take i ++ (γ.drop i).take (j - i) := by
    rw [← List.take_add]
    congr 1
    omega
  unfold wordDist
  have e : (A * (γ.take i).prod)⁻¹ * (A * (γ.take j).prod) =
      ((γ.drop i).take (j - i)).prod := by
    rw [hsplit, List.prod_append]
    group
  rw [e, wordNorm_prod_take hS (isGeodesicWord_drop hS hγ i) (j - i),
    List.length_take, List.length_drop]
  omega

/-- A middle segment of a word visits only vertices of the whole word. -/
theorem mem_listPoints_of_mem_drop_take {b : Q} {γ : List Q} {i k : ℕ} {q : Q}
    (hq : q ∈ listPoints (b * (γ.take i).prod) ((γ.drop i).take k)) :
    q ∈ listPoints b γ := by
  rw [mem_listPoints_iff] at hq ⊢
  obtain ⟨m, rfl⟩ := hq
  refine ⟨i + min m k, ?_⟩
  rw [List.take_take, List.take_add, List.prod_append, mul_assoc]

end DiscreteStokes
end GroupApproximation

#audit_axioms GroupApproximation.DiscreteStokes.mem_listPoints_revList
#audit_axioms GroupApproximation.DiscreteStokes.wordDist_take_of_geodesic
#audit_axioms GroupApproximation.DiscreteStokes.mem_listPoints_of_mem_drop_take
