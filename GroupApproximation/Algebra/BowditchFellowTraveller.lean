import GroupApproximation.Algebra.BowditchH4

/-!
# Fellow travelling from Bowditch's H4

Bowditch's Lemma 6.2.1 (*Notes on Gromov's hyperbolicity criterion*): in an
`(r, L)`-H4 space, two geodesics from the same point whose other endpoints are at
distance at most `r` stay close.  The form proved here is the one the rest of
Section 6.2 uses: if both endpoints of a geodesic word `δ` are within `r` of the
vertices of a geodesic word `γ`, then every vertex of `δ` is within `r + L` of them.

Proof: take a vertex of `δ` further than `r + L`.  Walk back to the last vertex at
distance at most `r` and forward to the first one.  The distance moves by one per
letter, so both endpoints of that stretch are at distance exactly `r`, and every
vertex in between is further.  H4 applies to the stretch, a geodesic of length
`b - a`: `3 (b - a) ≤ (b - a) + L`.  So the stretch has length at most `L / 2`, and the
far vertex is within that of a vertex at distance `r`, a contradiction.
-/

namespace GroupApproximation
namespace DiscreteStokes

open WordMetric

universe v

variable {Q : Type v} [Group Q]

/-- The distance to a list moves by at most the distance between the points. -/
theorem distToList_le_add_wordDist {S : Set Q} (hS : IsSymmetricGeneratingSet S)
    {P : List Q} (hP : P ≠ []) (g h : Q) :
    distToList S g P ≤ distToList S h P + wordDist S g h := by
  obtain ⟨p, hp, hpd⟩ := exists_mem_distToList_eq S h hP
  have h1 := distToList_le_of_mem S g hp
  have h2 := wordDist_triangle hS g h p
  omega

/-- The vertices of a middle segment of a word have indices in its range. -/
theorem exists_index_of_mem_listPoints_drop_take {X : Q} {δ : List Q} {a k : ℕ} {q : Q}
    (hq : q ∈ listPoints (X * (δ.take a).prod) ((δ.drop a).take k)) :
    ∃ j, a ≤ j ∧ j ≤ a + k ∧ q = X * (δ.take j).prod := by
  rw [mem_listPoints_iff] at hq
  obtain ⟨m, rfl⟩ := hq
  refine ⟨a + min m k, by omega, by omega, ?_⟩
  rw [List.take_take, List.take_add, List.prod_append, mul_assoc]

/-- **Bowditch's Lemma 6.2.1.**  In an `(r, L)`-H4 Cayley graph, if both endpoints of
a geodesic word `δ` are within `r` of the vertices of a geodesic word `γ`, every vertex
of `δ` is within `r + L` of them. -/
theorem distToList_le_of_bowditchH4 {S : Set Q} (hS : IsSymmetricGeneratingSet S)
    {r L : ℕ} (hH4 : BowditchH4 S r L) {A : Q} {γ : List Q}
    (hγ : IsGeodesicWord S γ γ.prod) {X : Q} {δ : List Q} (hδ : IsGeodesicWord S δ δ.prod)
    (hstart : distToList S X (listPoints A γ) ≤ r)
    (hend : distToList S (X * δ.prod) (listPoints A γ) ≤ r) :
    ∀ q ∈ listPoints X δ, distToList S q (listPoints A γ) ≤ r + L := by
  intro q hq
  obtain ⟨m, hm, rfl⟩ := exists_index_of_mem_listPoints hq
  have hP : listPoints A γ ≠ [] := listPoints_ne_nil A γ
  have hδletters : ∀ x ∈ δ, x ∈ S := hδ.isWord.letters
  have hf0 : distToList S (X * (δ.take 0).prod) (listPoints A γ) ≤ r := by
    simpa using hstart
  have hfend : distToList S (X * (δ.take δ.length).prod) (listPoints A γ) ≤ r := by
    rw [List.take_length]
    exact hend
  have hstep : ∀ k, k < δ.length →
      wordDist S (X * (δ.take k).prod) (X * (δ.take (k + 1)).prod) = 1 := by
    intro k hk
    rw [wordDist_take_of_geodesic hS hδ X (Nat.le_succ k) (by omega)]
    omega
  have hlip₁ : ∀ k, k < δ.length →
      distToList S (X * (δ.take (k + 1)).prod) (listPoints A γ) ≤
        distToList S (X * (δ.take k).prod) (listPoints A γ) + 1 := by
    intro k hk
    have h := distToList_le_add_wordDist hS hP (X * (δ.take (k + 1)).prod)
      (X * (δ.take k).prod)
    have hc := wordDist_comm hS (X * (δ.take (k + 1)).prod) (X * (δ.take k).prod)
    have hs := hstep k hk
    omega
  have hlip₂ : ∀ k, k < δ.length →
      distToList S (X * (δ.take k).prod) (listPoints A γ) ≤
        distToList S (X * (δ.take (k + 1)).prod) (listPoints A γ) + 1 := by
    intro k hk
    have h := distToList_le_add_wordDist hS hP (X * (δ.take k).prod)
      (X * (δ.take (k + 1)).prod)
    have hs := hstep k hk
    omega
  by_contra hcon
  have hcon' : r + L < distToList S (X * (δ.take m).prod) (listPoints A γ) :=
    not_le.mp hcon
  have hm_lt : m < δ.length := by
    rcases lt_or_eq_of_le hm with h | h
    · exact h
    · rw [h] at hcon'
      omega
  set a := Nat.findGreatest
    (fun k => distToList S (X * (δ.take k).prod) (listPoints A γ) ≤ r) m with ha_def
  have ha_spec : distToList S (X * (δ.take a).prod) (listPoints A γ) ≤ r :=
    Nat.findGreatest_spec
      (P := fun k => distToList S (X * (δ.take k).prod) (listPoints A γ) ≤ r)
      (Nat.zero_le m) hf0
  have ha_le : a ≤ m :=
    Nat.findGreatest_le (P := fun k => distToList S (X * (δ.take k).prod) (listPoints A γ) ≤ r) m
  have ha_greatest : ∀ k, a < k → k ≤ m →
      ¬ distToList S (X * (δ.take k).prod) (listPoints A γ) ≤ r :=
    fun k hk hkm => Nat.findGreatest_is_greatest
      (P := fun k => distToList S (X * (δ.take k).prod) (listPoints A γ) ≤ r) hk hkm
  have ha_lt : a < m := by
    rcases lt_or_eq_of_le ha_le with h | h
    · exact h
    · exfalso
      rw [h] at ha_spec
      omega
  have hexb : ∃ k, m < k ∧ distToList S (X * (δ.take k).prod) (listPoints A γ) ≤ r :=
    ⟨δ.length, hm_lt, hfend⟩
  set b := Nat.find hexb with hb_def
  have hb_spec : m < b ∧ distToList S (X * (δ.take b).prod) (listPoints A γ) ≤ r :=
    Nat.find_spec hexb
  have hb_min : ∀ k, k < b →
      ¬ (m < k ∧ distToList S (X * (δ.take k).prod) (listPoints A γ) ≤ r) :=
    fun k hk => Nat.find_min hexb hk
  have hb_le : b ≤ δ.length := Nat.find_min' hexb ⟨hm_lt, hfend⟩
  have hfar : ∀ k, a < k → k < b →
      r < distToList S (X * (δ.take k).prod) (listPoints A γ) := by
    intro k hak hkb
    by_cases hkm : k ≤ m
    · exact not_le.mp (ha_greatest k hak hkm)
    · exact not_le.mp (fun hle => hb_min k hkb ⟨by omega, hle⟩)
  have ha_eq : distToList S (X * (δ.take a).prod) (listPoints A γ) = r := by
    have h1 := hfar (a + 1) (by omega) (by omega)
    have h2 := hlip₁ a (by omega)
    omega
  have hb_eq : distToList S (X * (δ.take b).prod) (listPoints A γ) = r := by
    have h1 := hfar (b - 1) (by omega) (by omega)
    have h2 := hlip₂ (b - 1) (by omega)
    have e : b - 1 + 1 = b := by omega
    rw [e] at h2
    omega
  have hβletters : ∀ x ∈ (δ.drop a).take (b - a), x ∈ S :=
    fun x hx => hδletters x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  have hsplit : δ.take b = δ.take a ++ (δ.drop a).take (b - a) := by
    rw [← List.take_add]
    congr 1
    omega
  have hβend : X * (δ.take a).prod * ((δ.drop a).take (b - a)).prod = X * (δ.take b).prod := by
    rw [hsplit, List.prod_append, mul_assoc]
  have havoid : ∀ q ∈ listPoints (X * (δ.take a).prod) ((δ.drop a).take (b - a)),
      r ≤ distToList S q (listPoints A γ) := by
    intro q hq
    obtain ⟨j, haj, hjb, rfl⟩ := exists_index_of_mem_listPoints_drop_take hq
    rcases lt_or_eq_of_le haj with h | h
    · rcases lt_or_eq_of_le (show j ≤ b by omega) with h' | h'
      · exact (hfar j h h').le
      · rw [h']
        exact hb_eq.ge
    · rw [← h]
      exact ha_eq.ge
  have hH := hH4 A γ hγ (X * (δ.take a).prod) ((δ.drop a).take (b - a)) hβletters ha_eq
    (by rw [hβend]; exact hb_eq) havoid
  rw [hβend, wordDist_take_of_geodesic hS hδ X (by omega) hb_le, List.length_take,
    List.length_drop] at hH
  have hma := distToList_le_add_wordDist hS hP (X * (δ.take m).prod) (X * (δ.take a).prod)
  have hdma : wordDist S (X * (δ.take m).prod) (X * (δ.take a).prod) = m - a := by
    rw [wordDist_comm hS, wordDist_take_of_geodesic hS hδ X ha_le hm]
  omega

end DiscreteStokes
end GroupApproximation

#audit_axioms GroupApproximation.DiscreteStokes.distToList_le_add_wordDist
#audit_axioms GroupApproximation.DiscreteStokes.distToList_le_of_bowditchH4
