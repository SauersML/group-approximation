import GroupApproximation.Algebra.BowditchTriangle

/-!
# Centres of geodesic triangles

Bowditch's Lemma 6.2.3 (*Notes on Gromov's hyperbolicity criterion*): in an
`(r, L)`-H4 space every geodesic triangle has a *centre*, a point within
`M = 10 R + L` of all three sides, where `R = 4 r + L` is the constant of the corner
lemma.  This module records the notion of centre for a cyclic triangle and proves
the heart of Bowditch's argument, `exists_centre_of_maxMiddle`.

## The argument

Label the corners as Bowditch does: `A, D` on `[X, Y]`, `C, E` on `[Y, Z]`, `F, B` on
`[Z, X]`, in the cyclic order `X A D Y C E Z F B X`, with `d(A, B)`, `d(C, D)` and
`d(E, F)` at most `R`.  Suppose the middle `[A, D]` is at least as long as the other
two middles `[C, E]` and `[F, B]`.  Bowditch's detour runs from the last exit `G` of
the geodesic `[A, B]` from the `r`-neighbourhood of `[X, Y]`, to `B`, back along
`[Z, X]` to `F`, across `[F, E]`, and back along `[Y, Z]` to `C`, which is at distance
exactly `r` from `[X, Y]` (so Bowditch's `H` is `C` here).  Every vertex of the detour
is at distance at least `r` from `[X, Y]`, unless a vertex of `[F, E]` comes closer, and
such a vertex is itself a centre.  H4 bounds `3 d(G, C)` by the length of the detour,
at most `2 R + 2 d(A, D)`, and `d(A, D) ≤ d(G, C) + 2 R`.  So `d(A, D) ≤ 8 R + L`, and
`A` is within `9 R + L` of all three sides.
-/

namespace GroupApproximation
namespace DiscreteStokes

open WordMetric

universe v

variable {Q : Type v} [Group Q]

/-- A **centre** of the cyclic triangle with sides `γ₁` read from `V₁`, `γ₂` read from
`V₂` and `γ₃` read from `V₃`, at constant `M`: a point within `M` of all three sides. -/
structure IsCentre (S : Set Q) (M : ℕ) (V₁ V₂ V₃ : Q) (γ₁ γ₂ γ₃ : List Q) (W : Q) :
    Prop where
  near₁ : distToList S W (listPoints V₁ γ₁) ≤ M
  near₂ : distToList S W (listPoints V₂ γ₂) ≤ M
  near₃ : distToList S W (listPoints V₃ γ₃) ≤ M

/-- Rotating the triangle keeps its centres. -/
theorem IsCentre.rotate {S : Set Q} {M : ℕ} {V₁ V₂ V₃ : Q} {γ₁ γ₂ γ₃ : List Q} {W : Q}
    (h : IsCentre S M V₁ V₂ V₃ γ₁ γ₂ γ₃ W) : IsCentre S M V₂ V₃ V₁ γ₂ γ₃ γ₁ W :=
  ⟨h.near₂, h.near₃, h.near₁⟩

/-- The vertices of a final segment of a word have indices in its range. -/
theorem exists_index_of_mem_listPoints_drop {X : Q} {δ : List Q} {a : ℕ} {q : Q}
    (hq : q ∈ listPoints (X * (δ.take a).prod) (δ.drop a)) :
    ∃ j, a ≤ j ∧ q = X * (δ.take j).prod := by
  rw [mem_listPoints_iff] at hq
  obtain ⟨m, rfl⟩ := hq
  refine ⟨a + m, by omega, ?_⟩
  rw [List.take_add, List.prod_append, mul_assoc]

/-- **The last exit from a neighbourhood.**  A geodesic word `ω` read from `P`,
starting within `r` of a list of vertices and ending at distance at least `r` from it,
has a vertex at distance exactly `r` from which on every vertex stays at distance at
least `r`. -/
theorem exists_exit_index {S : Set Q} (hS : IsSymmetricGeneratingSet S) {T : List Q}
    (hT : T ≠ []) {r : ℕ} {P : Q} {ω : List Q} (hω : IsGeodesicWord S ω ω.prod)
    (hstart : distToList S P T ≤ r) (hend : r ≤ distToList S (P * ω.prod) T) :
    ∃ g, g ≤ ω.length ∧ distToList S (P * (ω.take g).prod) T = r ∧
      ∀ t, g ≤ t → r ≤ distToList S (P * (ω.take t).prod) T := by
  have hf0 : distToList S (P * (ω.take 0).prod) T ≤ r := by
    simpa using hstart
  set g := Nat.findGreatest
    (fun t => distToList S (P * (ω.take t).prod) T ≤ r) ω.length with hg_def
  have hg_spec : distToList S (P * (ω.take g).prod) T ≤ r :=
    Nat.findGreatest_spec
      (P := fun t => distToList S (P * (ω.take t).prod) T ≤ r) (Nat.zero_le _) hf0
  have hg_le : g ≤ ω.length :=
    Nat.findGreatest_le (P := fun t => distToList S (P * (ω.take t).prod) T ≤ r) _
  have hg_greatest : ∀ t, g < t → t ≤ ω.length →
      ¬ distToList S (P * (ω.take t).prod) T ≤ r :=
    fun t ht htl => Nat.findGreatest_is_greatest
      (P := fun t => distToList S (P * (ω.take t).prod) T ≤ r) ht htl
  have hg_eq : distToList S (P * (ω.take g).prod) T = r := by
    rcases lt_or_eq_of_le hg_le with h | h
    · have h1 := not_le.mp (hg_greatest (g + 1) (by omega) (by omega))
      have h2 := (distToList_take_succ_le hS hT (X := P) hω h).1
      omega
    · have h3 : distToList S (P * (ω.take g).prod) T = distToList S (P * ω.prod) T := by
        rw [h, List.take_length]
      omega
  refine ⟨g, hg_le, hg_eq, ?_⟩
  intro t ht
  by_cases htl : t ≤ ω.length
  · rcases lt_or_eq_of_le ht with h | h
    · exact (not_le.mp (hg_greatest t h htl)).le
    · rw [← h]
      exact hg_eq.ge
  · rw [List.take_of_length_le (by omega)]
    exact hend

/-- **Bowditch's detour at the longest middle.**  In the cyclic triangle with sides
`γ₁` from `V₁`, `γ₂` from `V₂`, `γ₃` from `V₃`, take the corner points
`A = V₁ γ₁[..a]`, `D = V₁ γ₁[..d]`, `C = V₂ γ₂[..c]`, `E = V₂ γ₂[..e]`,
`F = V₃ γ₃[..f]`, `B = V₃ γ₃[..b]` in Bowditch's cyclic order, with
`d(A, B)`, `d(C, D)`, `d(F, E)` at most `R`, with `[Z, B]` and `[C, Z]` at distance at
least `r` from `[X, Y]` and `C` at distance exactly `r`, and with `[A, D]` the longest
middle.  Then the triangle has a centre at constant `M ≥ 9 R + L`. -/
theorem exists_centre_of_maxMiddle {S : Set Q} (hS : IsSymmetricGeneratingSet S)
    {r L R M : ℕ} (hH4 : BowditchH4 S r L) (hrM : r ≤ M) (hRM : 9 * R + L ≤ M)
    {V₁ V₂ V₃ : Q} {γ₁ γ₂ γ₃ : List Q} (hγ₁ : IsGeodesicWord S γ₁ γ₁.prod)
    (hγ₂ : IsGeodesicWord S γ₂ γ₂.prod) (hγ₃ : IsGeodesicWord S γ₃ γ₃.prod)
    {a d c e f b : ℕ} (had : a ≤ d) (hd : d ≤ γ₁.length) (hce : c ≤ e)
    (hfb : f ≤ b)
    (hAB : wordDist S (V₁ * (γ₁.take a).prod) (V₃ * (γ₃.take b).prod) ≤ R)
    (hBfar : ∀ s, s ≤ b → r ≤ distToList S (V₃ * (γ₃.take s).prod) (listPoints V₁ γ₁))
    (hC : distToList S (V₂ * (γ₂.take c).prod) (listPoints V₁ γ₁) = r)
    (hCfar : ∀ t, c ≤ t → r ≤ distToList S (V₂ * (γ₂.take t).prod) (listPoints V₁ γ₁))
    (hCD : wordDist S (V₂ * (γ₂.take c).prod) (V₁ * (γ₁.take d).prod) ≤ R)
    (hFE : wordDist S (V₃ * (γ₃.take f).prod) (V₂ * (γ₂.take e).prod) ≤ R)
    (hmax₂ : e - c ≤ d - a) (hmax₃ : b - f ≤ d - a) :
    ∃ W, IsCentre S M V₁ V₂ V₃ γ₁ γ₂ γ₃ W := by
  have hP₁ : listPoints V₁ γ₁ ≠ [] := listPoints_ne_nil V₁ γ₁
  -- the geodesic word `[F, E]`
  obtain ⟨ωFE, hωFE⟩ := exists_isGeodesicWord hS
    ((V₃ * (γ₃.take f).prod)⁻¹ * (V₂ * (γ₂.take e).prod))
  have hωFEletters : ∀ x ∈ ωFE, x ∈ S := hωFE.isWord.letters
  have hωFEprod : V₃ * (γ₃.take f).prod * ωFE.prod = V₂ * (γ₂.take e).prod := by
    rw [hωFE.isWord.prod_eq]
    group
  have hωFElen : ωFE.length ≤ R := by
    rw [hωFE.length_eq]
    exact hFE
  by_cases hnear : ∃ q ∈ listPoints (V₃ * (γ₃.take f).prod) ωFE,
      distToList S q (listPoints V₁ γ₁) < r
  · -- a vertex of `[F, E]` close to `[X, Y]` is a centre
    obtain ⟨q, hq, hqd⟩ := hnear
    refine ⟨q, ⟨by omega, ?_, ?_⟩⟩
    · have h1 := distToList_le_of_mem S q (take_mem_listPoints V₂ γ₂ e)
      have h2 := wordDist_end_le_of_mem hωFEletters hq
      rw [hωFEprod] at h2
      omega
    · have h1 := distToList_le_of_mem S q (take_mem_listPoints V₃ γ₃ f)
      have h2 := wordDist_start_le_of_mem hωFEletters hq
      have h3 := wordDist_comm hS q (V₃ * (γ₃.take f).prod)
      omega
  have hfarFE : ∀ q ∈ listPoints (V₃ * (γ₃.take f).prod) ωFE,
      r ≤ distToList S q (listPoints V₁ γ₁) :=
    fun q hq => not_lt.mp (fun h => hnear ⟨q, hq, h⟩)
  -- the geodesic word `[A, B]` and its last exit `G`
  obtain ⟨ωAB, hωAB⟩ := exists_isGeodesicWord hS
    ((V₁ * (γ₁.take a).prod)⁻¹ * (V₃ * (γ₃.take b).prod))
  have hωABletters : ∀ x ∈ ωAB, x ∈ S := hωAB.isWord.letters
  have hωABprod : V₁ * (γ₁.take a).prod * ωAB.prod = V₃ * (γ₃.take b).prod := by
    rw [hωAB.isWord.prod_eq]
    group
  have hωABlen : ωAB.length ≤ R := by
    rw [hωAB.length_eq]
    exact hAB
  have hωABgeo : IsGeodesicWord S ωAB ωAB.prod := by
    refine ⟨⟨hωABletters, rfl⟩, ?_⟩
    rw [hωAB.isWord.prod_eq]
    exact hωAB.length_eq
  obtain ⟨g, _hg_le, hGr, hGfar⟩ := exists_exit_index hS hP₁ hωABgeo
    (P := V₁ * (γ₁.take a).prod)
    (by rw [distToList_eq_zero_of_mem S (take_mem_listPoints V₁ γ₁ a)]; exact Nat.zero_le _)
    (by rw [hωABprod]; exact hBfar b le_rfl)
  have hGprod : V₁ * (γ₁.take a).prod * (ωAB.take g).prod * (ωAB.drop g).prod =
      V₃ * (γ₃.take b).prod := by
    rw [← hωABprod, ← List.prod_take_mul_prod_drop ωAB g]
    group
  -- the segments `[F, B]` of `γ₃` and `[C, E]` of `γ₂`
  have hsplit₃ : γ₃.take b = γ₃.take f ++ (γ₃.drop f).take (b - f) := by
    rw [← List.take_add]
    congr 1
    omega
  have hseg₃prod : V₃ * (γ₃.take f).prod * ((γ₃.drop f).take (b - f)).prod =
      V₃ * (γ₃.take b).prod := by
    rw [hsplit₃, List.prod_append, mul_assoc]
  have hsplit₂ : γ₂.take e = γ₂.take c ++ (γ₂.drop c).take (e - c) := by
    rw [← List.take_add]
    congr 1
    omega
  have hseg₂prod : V₂ * (γ₂.take c).prod * ((γ₂.drop c).take (e - c)).prod =
      V₂ * (γ₂.take e).prod := by
    rw [hsplit₂, List.prod_append, mul_assoc]
  have hβ₂ : V₃ * (γ₃.take b).prod * (revList ((γ₃.drop f).take (b - f))).prod =
      V₃ * (γ₃.take f).prod := by
    rw [prod_revList, ← hseg₃prod]
    group
  have hβ₄ : V₂ * (γ₂.take e).prod * (revList ((γ₂.drop c).take (e - c))).prod =
      V₂ * (γ₂.take c).prod := by
    rw [prod_revList, ← hseg₂prod]
    group
  -- the detour `α = [G, B] [B, F] [F, E] [E, C]`
  have hbase₂ : V₁ * (γ₁.take a).prod * (ωAB.take g).prod *
      (ωAB.drop g ++ revList ((γ₃.drop f).take (b - f))).prod = V₃ * (γ₃.take f).prod := by
    simp only [List.prod_append, ← mul_assoc]
    rw [hGprod, hβ₂]
  have hbase₃ : V₁ * (γ₁.take a).prod * (ωAB.take g).prod *
      (ωAB.drop g ++ revList ((γ₃.drop f).take (b - f)) ++ ωFE).prod =
        V₂ * (γ₂.take e).prod := by
    simp only [List.prod_append, ← mul_assoc]
    rw [hGprod, hβ₂, hωFEprod]
  have hαprod : V₁ * (γ₁.take a).prod * (ωAB.take g).prod *
      (ωAB.drop g ++ revList ((γ₃.drop f).take (b - f)) ++ ωFE ++
        revList ((γ₂.drop c).take (e - c))).prod = V₂ * (γ₂.take c).prod := by
    simp only [List.prod_append, ← mul_assoc]
    rw [hGprod, hβ₂, hωFEprod, hβ₄]
  have hαletters : ∀ x ∈ ωAB.drop g ++ revList ((γ₃.drop f).take (b - f)) ++ ωFE ++
      revList ((γ₂.drop c).take (e - c)), x ∈ S := by
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with ((hx | hx) | hx) | hx
    · exact hωABletters x (List.mem_of_mem_drop hx)
    · exact letters_revList hS (fun y hy => hγ₃.isWord.letters y
        (List.mem_of_mem_drop (List.mem_of_mem_take hy))) x hx
    · exact hωFEletters x hx
    · exact letters_revList hS (fun y hy => hγ₂.isWord.letters y
        (List.mem_of_mem_drop (List.mem_of_mem_take hy))) x hx
  have hαfar : ∀ q ∈ listPoints (V₁ * (γ₁.take a).prod * (ωAB.take g).prod)
      (ωAB.drop g ++ revList ((γ₃.drop f).take (b - f)) ++ ωFE ++
        revList ((γ₂.drop c).take (e - c))),
      r ≤ distToList S q (listPoints V₁ γ₁) := by
    intro q hq
    rw [mem_listPoints_append, mem_listPoints_append, mem_listPoints_append] at hq
    rcases hq with ((hq | hq) | hq) | hq
    · obtain ⟨j, hj, rfl⟩ := exists_index_of_mem_listPoints_drop hq
      exact hGfar j hj
    · rw [hGprod, ← hseg₃prod, mem_listPoints_revList] at hq
      obtain ⟨j, _hfj, hjb, rfl⟩ := exists_index_of_mem_listPoints_drop_take hq
      exact hBfar j (by omega)
    · rw [hbase₂] at hq
      exact hfarFE q hq
    · rw [hbase₃, ← hseg₂prod, mem_listPoints_revList] at hq
      obtain ⟨j, hcj, _hje, rfl⟩ := exists_index_of_mem_listPoints_drop_take hq
      exact hCfar j hcj
  have hH := hH4 V₁ γ₁ hγ₁ (V₁ * (γ₁.take a).prod * (ωAB.take g).prod)
    (ωAB.drop g ++ revList ((γ₃.drop f).take (b - f)) ++ ωFE ++
      revList ((γ₂.drop c).take (e - c))) hαletters hGr (by rw [hαprod]; exact hC) hαfar
  rw [hαprod] at hH
  simp only [List.length_append, length_revList, List.length_drop, List.length_take] at hH
  -- `d(A, D) ≤ 8 R + L`
  have hAD : wordDist S (V₁ * (γ₁.take a).prod) (V₁ * (γ₁.take d).prod) = d - a :=
    wordDist_take_of_geodesic hS hγ₁ V₁ had hd
  have hAG : wordDist S (V₁ * (γ₁.take a).prod)
      (V₁ * (γ₁.take a).prod * (ωAB.take g).prod) ≤ ωAB.length :=
    wordDist_start_le_of_mem hωABletters (take_mem_listPoints _ ωAB g)
  have ht₁ := wordDist_triangle hS (V₁ * (γ₁.take a).prod)
    (V₁ * (γ₁.take a).prod * (ωAB.take g).prod) (V₁ * (γ₁.take d).prod)
  have ht₂ := wordDist_triangle hS (V₁ * (γ₁.take a).prod * (ωAB.take g).prod)
    (V₂ * (γ₂.take c).prod) (V₁ * (γ₁.take d).prod)
  have hmid : d - a ≤ 8 * R + L := by omega
  -- `A` is a centre
  refine ⟨V₁ * (γ₁.take a).prod, ⟨?_, ?_, ?_⟩⟩
  · rw [distToList_eq_zero_of_mem S (take_mem_listPoints V₁ γ₁ a)]
    exact Nat.zero_le _
  · have h1 := distToList_le_of_mem S (V₁ * (γ₁.take a).prod) (take_mem_listPoints V₂ γ₂ c)
    have h2 := wordDist_triangle hS (V₁ * (γ₁.take a).prod) (V₁ * (γ₁.take d).prod)
      (V₂ * (γ₂.take c).prod)
    have h3 := wordDist_comm hS (V₁ * (γ₁.take d).prod) (V₂ * (γ₂.take c).prod)
    omega
  · have h1 := distToList_le_of_mem S (V₁ * (γ₁.take a).prod) (take_mem_listPoints V₃ γ₃ b)
    omega

end DiscreteStokes
end GroupApproximation

#audit_axioms GroupApproximation.DiscreteStokes.IsCentre.rotate
#audit_axioms GroupApproximation.DiscreteStokes.exists_index_of_mem_listPoints_drop
#audit_axioms GroupApproximation.DiscreteStokes.exists_exit_index
#audit_axioms GroupApproximation.DiscreteStokes.exists_centre_of_maxMiddle
