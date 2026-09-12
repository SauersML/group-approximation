import GroupApproximation.Algebra.BowditchFellowTraveller

/-!
# Corners of geodesic triangles in an H4 Cayley graph

Bowditch's Lemma 6.2.2 (*Notes on Gromov's hyperbolicity criterion*): two geodesics
`[X, Y]` and `[X, Z]` from a common point, with each far endpoint at distance at least
`R = 4 r + L` from the other geodesic, fellow travel up to a pair of points
`A ∈ [X, Y]`, `B ∈ [X, Z]` and then separate:

* the rest `[A, Y]` stays at distance at least `r` from `[X, Z]`;
* the rest `[B, Z]` stays at distance at least `r` from `[X, Y]`;
* the initial pieces `[X, A]` and `[X, B]` are within `R` of each other;
* `r ≤ d(A, B) ≤ R`.

`A` is the last vertex of `[X, Y]` within `r` of `[X, Z]`, `C` its nearest vertex on
`[X, Z]`, and `B` the vertex `3 r + L` further along `[X, Z]` from `C`.  The fellow
travelling of the initial pieces is `distToList_le_of_bowditchH4` applied twice; the
separation of `[B, Z]` is the observation that a point of `[B, Z]` close to `[X, Y]`
would be close to `[X, A]`, hence within `r + L` of `[X, C]`, while `[X, C]` and
`[B, Z]` are `3 r + L` apart along the geodesic `[X, Z]`.

Our constants: `J = r + L` in place of Bowditch's `r + L/4`, which only enlarges `R`.
-/

namespace GroupApproximation
namespace DiscreteStokes

open WordMetric

universe v

variable {Q : Type v} [Group Q]

/-- Distance to a list can only drop when the list grows. -/
theorem distToList_le_of_subset (S : Set Q) (g : Q) {P P' : List Q} (hP : P ≠ [])
    (hsub : ∀ p ∈ P, p ∈ P') : distToList S g P' ≤ distToList S g P := by
  obtain ⟨p, hp, hpd⟩ := exists_mem_distToList_eq S g hP
  rw [← hpd]
  exact distToList_le_of_mem S g (hsub p hp)

/-- The vertices of an initial segment are vertices of a longer initial segment. -/
theorem mem_listPoints_take_of_le {X : Q} {δ : List Q} {c k : ℕ} (hck : c ≤ k) {q : Q}
    (hq : q ∈ listPoints X (δ.take c)) : q ∈ listPoints X (δ.take k) := by
  rw [mem_listPoints_iff] at hq ⊢
  obtain ⟨m, rfl⟩ := hq
  refine ⟨min m c, ?_⟩
  rw [List.take_take, List.take_take, min_assoc, min_eq_left hck]

/-- The vertex at index `t` of a word read from `X`. -/
theorem take_mem_listPoints (X : Q) (δ : List Q) (t : ℕ) :
    X * (δ.take t).prod ∈ listPoints X δ :=
  (mem_listPoints_iff X δ _).mpr ⟨t, rfl⟩

/-- Consecutive vertices of a geodesic word are at distance one, so the distance to a
list changes by at most one between them. -/
theorem distToList_take_succ_le {S : Set Q} (hS : IsSymmetricGeneratingSet S) {P : List Q}
    (hP : P ≠ []) {X : Q} {δ : List Q} (hδ : IsGeodesicWord S δ δ.prod) {k : ℕ}
    (hk : k < δ.length) :
    distToList S (X * (δ.take (k + 1)).prod) P ≤ distToList S (X * (δ.take k).prod) P + 1 ∧
      distToList S (X * (δ.take k).prod) P ≤ distToList S (X * (δ.take (k + 1)).prod) P + 1 := by
  have hs : wordDist S (X * (δ.take k).prod) (X * (δ.take (k + 1)).prod) = 1 := by
    rw [wordDist_take_of_geodesic hS hδ X (Nat.le_succ k) (by omega)]
    omega
  have hc := wordDist_comm hS (X * (δ.take (k + 1)).prod) (X * (δ.take k).prod)
  have h₁ := distToList_le_add_wordDist hS hP (X * (δ.take (k + 1)).prod) (X * (δ.take k).prod)
  have h₂ := distToList_le_add_wordDist hS hP (X * (δ.take k).prod) (X * (δ.take (k + 1)).prod)
  omega

/-- **Bowditch's Lemma 6.2.2** in the Cayley graph, with `R = 4 r + L`. -/
theorem exists_corner_of_bowditchH4 {S : Set Q} (hS : IsSymmetricGeneratingSet S)
    {r L : ℕ} (hr : 0 < r) (hH4 : BowditchH4 S r L) {X : Q} {γ δ : List Q}
    (hγ : IsGeodesicWord S γ γ.prod) (hδ : IsGeodesicWord S δ δ.prod)
    (hY : 4 * r + L ≤ distToList S (X * γ.prod) (listPoints X δ))
    (hZ : 4 * r + L ≤ distToList S (X * δ.prod) (listPoints X γ)) :
    ∃ i k : ℕ, i ≤ γ.length ∧ k ≤ δ.length ∧
      distToList S (X * (γ.take i).prod) (listPoints X δ) = r ∧
      (∀ t, i ≤ t → r ≤ distToList S (X * (γ.take t).prod) (listPoints X δ)) ∧
      (∀ t, k ≤ t → t ≤ δ.length → r ≤ distToList S (X * (δ.take t).prod) (listPoints X γ)) ∧
      (∀ t, t ≤ k → distToList S (X * (δ.take t).prod) (listPoints X (γ.take i)) ≤ 4 * r + L) ∧
      (∀ t, t ≤ i → distToList S (X * (γ.take t).prod) (listPoints X (δ.take k)) ≤ r + L) ∧
      r ≤ wordDist S (X * (γ.take i).prod) (X * (δ.take k).prod) ∧
      wordDist S (X * (γ.take i).prod) (X * (δ.take k).prod) ≤ 4 * r + L := by
  have hPδ : listPoints X δ ≠ [] := listPoints_ne_nil X δ
  have hPγ : listPoints X γ ≠ [] := listPoints_ne_nil X γ
  -- `A`: the last vertex of `γ` within `r` of `δ`
  have hX0 : X * (γ.take 0).prod ∈ listPoints X δ := by
    simpa using start_mem_listPoints X δ
  have hf0 : distToList S (X * (γ.take 0).prod) (listPoints X δ) ≤ r := by
    rw [distToList_eq_zero_of_mem S hX0]
    exact Nat.zero_le _
  set i := Nat.findGreatest
    (fun t => distToList S (X * (γ.take t).prod) (listPoints X δ) ≤ r) γ.length with hi_def
  have hi_spec : distToList S (X * (γ.take i).prod) (listPoints X δ) ≤ r :=
    Nat.findGreatest_spec
      (P := fun t => distToList S (X * (γ.take t).prod) (listPoints X δ) ≤ r)
      (Nat.zero_le _) hf0
  have hi_le : i ≤ γ.length :=
    Nat.findGreatest_le (P := fun t => distToList S (X * (γ.take t).prod) (listPoints X δ) ≤ r) _
  have hi_greatest : ∀ t, i < t → t ≤ γ.length →
      ¬ distToList S (X * (γ.take t).prod) (listPoints X δ) ≤ r :=
    fun t ht htl => Nat.findGreatest_is_greatest
      (P := fun t => distToList S (X * (γ.take t).prod) (listPoints X δ) ≤ r) ht htl
  have hi_lt : i < γ.length := by
    rcases lt_or_eq_of_le hi_le with h | h
    · exact h
    · exfalso
      rw [h, List.take_length] at hi_spec
      omega
  have hA_eq : distToList S (X * (γ.take i).prod) (listPoints X δ) = r := by
    have h1 := not_le.mp (hi_greatest (i + 1) (by omega) (by omega))
    have h2 := (distToList_take_succ_le hS hPδ (X := X) hγ hi_lt).1
    omega
  have hfar_γ : ∀ t, i ≤ t → r ≤ distToList S (X * (γ.take t).prod) (listPoints X δ) := by
    intro t ht
    by_cases htl : t ≤ γ.length
    · rcases lt_or_eq_of_le ht with h | h
      · exact (not_le.mp (hi_greatest t h htl)).le
      · rw [← h, hA_eq]
    · have e : γ.take t = γ.take γ.length := by
        rw [List.take_of_length_le (by omega), List.take_length]
      rw [e]
      exact (not_le.mp (hi_greatest γ.length hi_lt le_rfl)).le
  -- `C`: the nearest vertex of `δ` to `A`
  obtain ⟨C, hCmem, hCd⟩ :=
    exists_mem_distToList_eq S (X * (γ.take i).prod) hPδ
  rw [hA_eq] at hCd
  obtain ⟨c, hc_le, rfl⟩ := exists_index_of_mem_listPoints hCmem
  -- `B`: the vertex `3 r + L` further along `δ`
  have hZA : 4 * r + L ≤ wordDist S (X * δ.prod) (X * (γ.take i).prod) :=
    le_trans hZ (distToList_le_of_mem S _ (take_mem_listPoints X γ i))
  have hCZ : wordDist S (X * (δ.take c).prod) (X * δ.prod) = δ.length - c := by
    have h := wordDist_take_of_geodesic hS hδ X hc_le le_rfl
    rwa [List.take_length] at h
  have htri : wordDist S (X * δ.prod) (X * (γ.take i).prod) ≤
      wordDist S (X * δ.prod) (X * (δ.take c).prod) +
        wordDist S (X * (δ.take c).prod) (X * (γ.take i).prod) :=
    wordDist_triangle hS _ _ _
  have hc₁ := wordDist_comm hS (X * δ.prod) (X * (δ.take c).prod)
  have hc₂ := wordDist_comm hS (X * (δ.take c).prod) (X * (γ.take i).prod)
  have hk_le : c + (3 * r + L) ≤ δ.length := by omega
  refine ⟨i, c + (3 * r + L), hi_le, hk_le, hA_eq, hfar_γ, ?_, ?_, ?_, ?_, ?_⟩
  · -- the rest `[B, Z]` stays `r` away from `γ`
    intro t ht htl
    by_contra hcon
    have hlt : distToList S (X * (δ.take t).prod) (listPoints X γ) < r := not_le.mp hcon
    obtain ⟨E, hEmem, hEd⟩ := exists_mem_distToList_eq S (X * (δ.take t).prod) hPγ
    obtain ⟨s, hs_le, rfl⟩ := exists_index_of_mem_listPoints hEmem
    have hEδ : distToList S (X * (γ.take s).prod) (listPoints X δ) < r := by
      have h1 := distToList_le_of_mem S (X * (γ.take s).prod) (take_mem_listPoints X δ t)
      have h2 := wordDist_comm hS (X * (γ.take s).prod) (X * (δ.take t).prod)
      omega
    have hsi : s < i := by
      by_contra h
      have := hfar_γ s (not_lt.mp h)
      omega
    -- `E` is within `r + L` of `[X, C]`
    have hft := distToList_le_of_bowditchH4 hS hH4 (A := X) (γ := δ.take c)
      (isGeodesicWord_take hS hδ c) (X := X) (δ := γ.take i) (isGeodesicWord_take hS hγ i)
      (by rw [distToList_eq_zero_of_mem S (start_mem_listPoints X _)]; exact Nat.zero_le _)
      (by
        have h := distToList_le_of_mem S (X * (γ.take i).prod) (end_mem_listPoints X (δ.take c))
        omega)
      (X * (γ.take s).prod)
      (by
        rw [mem_listPoints_iff]
        exact ⟨s, by rw [List.take_take, min_eq_left hsi.le]⟩)
    obtain ⟨F, hFmem, hFd⟩ :=
      exists_mem_distToList_eq S (X * (γ.take s).prod) (listPoints_ne_nil X (δ.take c))
    obtain ⟨u, hu_le, rfl⟩ := exists_index_of_mem_listPoints hFmem
    have hu : u ≤ c := by
      have := List.length_take_le c δ
      omega
    rw [List.take_take, min_eq_left (by omega : u ≤ c)] at hFd
    have hDF : wordDist S (X * (δ.take u).prod) (X * (δ.take t).prod) = t - u :=
      wordDist_take_of_geodesic hS hδ X (by omega) htl
    have ht₁ := wordDist_triangle hS (X * (δ.take u).prod) (X * (γ.take s).prod)
      (X * (δ.take t).prod)
    have hc₃ := wordDist_comm hS (X * (δ.take u).prod) (X * (γ.take s).prod)
    have hc₄ := wordDist_comm hS (X * (γ.take s).prod) (X * (δ.take t).prod)
    omega
  · -- `[X, B]` is within `R` of `[X, A]`
    intro t ht
    by_cases htc : t ≤ c
    · have hft := distToList_le_of_bowditchH4 hS hH4 (A := X) (γ := γ.take i)
        (isGeodesicWord_take hS hγ i) (X := X) (δ := δ.take c) (isGeodesicWord_take hS hδ c)
        (by rw [distToList_eq_zero_of_mem S (start_mem_listPoints X _)]; exact Nat.zero_le _)
        (by
          have h := distToList_le_of_mem S (X * (δ.take c).prod)
            (end_mem_listPoints X (γ.take i))
          have hc := wordDist_comm hS (X * (δ.take c).prod) (X * (γ.take i).prod)
          omega)
        (X * (δ.take t).prod)
        (by
          rw [mem_listPoints_iff]
          exact ⟨t, by rw [List.take_take, min_eq_left htc]⟩)
      omega
    · have h1 := distToList_le_of_mem S (X * (δ.take t).prod) (end_mem_listPoints X (γ.take i))
      have h2 := wordDist_triangle hS (X * (δ.take t).prod) (X * (δ.take c).prod)
        (X * (γ.take i).prod)
      have hc := wordDist_comm hS (X * (δ.take c).prod) (X * (γ.take i).prod)
      have h3 : wordDist S (X * (δ.take t).prod) (X * (δ.take c).prod) = t - c := by
        rw [wordDist_comm hS, wordDist_take_of_geodesic hS hδ X (by omega) (by omega)]
      omega
  · -- `[X, A]` is within `r + L` of `[X, B]`
    intro t ht
    have hft := distToList_le_of_bowditchH4 hS hH4 (A := X) (γ := δ.take c)
      (isGeodesicWord_take hS hδ c) (X := X) (δ := γ.take i) (isGeodesicWord_take hS hγ i)
      (by rw [distToList_eq_zero_of_mem S (start_mem_listPoints X _)]; exact Nat.zero_le _)
      (by
        have h := distToList_le_of_mem S (X * (γ.take i).prod) (end_mem_listPoints X (δ.take c))
        omega)
      (X * (γ.take t).prod)
      (by
        rw [mem_listPoints_iff]
        exact ⟨t, by rw [List.take_take, min_eq_left ht]⟩)
    have hsub := distToList_le_of_subset S (X * (γ.take t).prod) (listPoints_ne_nil X (δ.take c))
      (fun p hp => mem_listPoints_take_of_le (by omega : c ≤ c + (3 * r + L)) hp)
    omega
  · -- `r ≤ d(A, B)`
    have h := distToList_le_of_mem S (X * (γ.take i).prod)
      (take_mem_listPoints X δ (c + (3 * r + L)))
    omega
  · -- `d(A, B) ≤ R`
    have h1 := wordDist_triangle hS (X * (γ.take i).prod) (X * (δ.take c).prod)
      (X * (δ.take (c + (3 * r + L))).prod)
    have h2 : wordDist S (X * (δ.take c).prod) (X * (δ.take (c + (3 * r + L))).prod) =
        3 * r + L := by
      rw [wordDist_take_of_geodesic hS hδ X (by omega) hk_le]
      omega
    omega

end DiscreteStokes
end GroupApproximation

#audit_axioms GroupApproximation.DiscreteStokes.distToList_le_of_subset
#audit_axioms GroupApproximation.DiscreteStokes.exists_corner_of_bowditchH4
