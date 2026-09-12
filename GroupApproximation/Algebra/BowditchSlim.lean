import GroupApproximation.Algebra.BowditchCentreAssembly
import GroupApproximation.Algebra.HyperbolicSlimTriangles

/-!
# Slim triangles from H4

Bowditch's Proposition 6.2.4 (*Notes on Gromov's hyperbolicity criterion*): an
`(r, L)`-H4 space is hyperbolic.  Bowditch reads it off the centres of Lemma 6.2.3
(`exists_centre_of_bowditchH4`); in the betweenness form of
`Hyperbolic.IsSlimTriangles` this module does it as follows.

* **Fellow travelling with slack** (`distToList_le_of_bowditchH4_of_end`): a geodesic
  word starting within `r` of a geodesic `γ` and ending within `s` of it stays within
  `r + 2 s + L` of `γ`.  Take a far vertex, the last exit before it from the
  `r`-neighbourhood, and either the next entry along the word or, if there is none,
  the first entry along a shortest path from the endpoint to `γ`; H4 bounds the
  stretch between them.
* **Slim triangles** (`isSlimTriangles_of_bowditchH4`): given a point `p` between `x`
  and `y`, run a geodesic word through it, complete the triangle, and take a centre
  `W` with nearest points `W₁, W₂, W₃` on the sides.  The piece of `[x, y]` before `W₁`
  starts on `[z, x]` and ends within `2 M` of it, the piece after `W₁`, read backwards
  from `y`, starts on `[y, z]` and ends within `2 M` of it.
-/

namespace GroupApproximation
namespace DiscreteStokes

open WordMetric

universe v

variable {Q : Type v} [Group Q]

/-- The vertices of an initial segment of a word have indices in its range. -/
theorem exists_index_of_mem_listPoints_take {X : Q} {δ : List Q} {n : ℕ} {q : Q}
    (hq : q ∈ listPoints X (δ.take n)) : ∃ j, j ≤ n ∧ q = X * (δ.take j).prod := by
  rw [mem_listPoints_iff] at hq
  obtain ⟨i, rfl⟩ := hq
  exact ⟨min i n, min_le_right _ _, by rw [List.take_take]⟩

/-- **The first entry into a neighbourhood.**  A geodesic word `ω` read from `P`,
starting at distance at least `r` from a list of vertices and ending within `r` of it,
has a vertex at distance exactly `r` up to which every vertex stays at distance at
least `r`. -/
theorem exists_entry_index {S : Set Q} (hS : IsSymmetricGeneratingSet S) {T : List Q}
    (hT : T ≠ []) {r : ℕ} {P : Q} {ω : List Q} (hω : IsGeodesicWord S ω ω.prod)
    (hstart : r ≤ distToList S P T) (hend : distToList S (P * ω.prod) T ≤ r) :
    ∃ n, n ≤ ω.length ∧ distToList S (P * (ω.take n).prod) T = r ∧
      ∀ t, t ≤ n → r ≤ distToList S (P * (ω.take t).prod) T := by
  have hlen : distToList S (P * (ω.take ω.length).prod) T ≤ r := by
    rw [List.take_length]
    exact hend
  have hex : ∃ t, distToList S (P * (ω.take t).prod) T ≤ r := ⟨ω.length, hlen⟩
  have hn_spec : distToList S (P * (ω.take (Nat.find hex)).prod) T ≤ r := Nat.find_spec hex
  have hn_min : ∀ t, t < Nat.find hex → ¬ distToList S (P * (ω.take t).prod) T ≤ r :=
    fun t ht => Nat.find_min hex ht
  have hn_le : Nat.find hex ≤ ω.length := Nat.find_min' hex hlen
  have hn_eq : distToList S (P * (ω.take (Nat.find hex)).prod) T = r := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · have e : distToList S (P * (ω.take (Nat.find hex)).prod) T = distToList S P T := by
        rw [h0]
        simp
      omega
    · have h1 := not_le.mp (hn_min (Nat.find hex - 1) (by omega))
      have h2 := (distToList_take_succ_le hS hT (X := P) hω
        (k := Nat.find hex - 1) (by omega)).2
      have e : Nat.find hex - 1 + 1 = Nat.find hex := by omega
      rw [e] at h2
      omega
  refine ⟨Nat.find hex, hn_le, hn_eq, ?_⟩
  intro t ht
  rcases lt_or_eq_of_le ht with h | h
  · exact (not_le.mp (hn_min t h)).le
  · rw [h]
    exact hn_eq.ge

/-- H4 along a path in two pieces. -/
theorem three_mul_wordDist_le_of_bowditchH4_append {S : Set Q} {r L : ℕ}
    (hH4 : BowditchH4 S r L) {A : Q} {γ : List Q} (hγ : IsGeodesicWord S γ γ.prod)
    {X : Q} {β₁ β₂ : List Q} (h₁ : ∀ x ∈ β₁, x ∈ S) (h₂ : ∀ x ∈ β₂, x ∈ S)
    (hX : distToList S X (listPoints A γ) = r)
    (hY : distToList S (X * β₁.prod * β₂.prod) (listPoints A γ) = r)
    (hv₁ : ∀ q ∈ listPoints X β₁, r ≤ distToList S q (listPoints A γ))
    (hv₂ : ∀ q ∈ listPoints (X * β₁.prod) β₂, r ≤ distToList S q (listPoints A γ)) :
    3 * wordDist S X (X * β₁.prod * β₂.prod) ≤ β₁.length + β₂.length + L := by
  have hl : ∀ x ∈ β₁ ++ β₂, x ∈ S := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h₁ x hx
    · exact h₂ x hx
  have hprod : X * (β₁ ++ β₂).prod = X * β₁.prod * β₂.prod := by
    rw [List.prod_append, mul_assoc]
  have h := hH4 A γ hγ X (β₁ ++ β₂) hl hX (by rw [hprod]; exact hY) (by
    intro q hq
    rcases (mem_listPoints_append X β₁ β₂ q).mp hq with hq | hq
    · exact hv₁ q hq
    · exact hv₂ q hq)
  rw [hprod, List.length_append] at h
  exact h

/-- **Fellow travelling with slack.**  In an `(r, L)`-H4 Cayley graph, a geodesic word
`δ` starting within `r` of the vertices of a geodesic word `γ` and ending within `s` of
them has every vertex within `r + 2 s + L` of them. -/
theorem distToList_le_of_bowditchH4_of_end {S : Set Q} (hS : IsSymmetricGeneratingSet S)
    {r L : ℕ} (hH4 : BowditchH4 S r L) {A : Q} {γ : List Q}
    (hγ : IsGeodesicWord S γ γ.prod) {X : Q} {δ : List Q} (hδ : IsGeodesicWord S δ δ.prod)
    {s : ℕ} (hstart : distToList S X (listPoints A γ) ≤ r)
    (hend : distToList S (X * δ.prod) (listPoints A γ) ≤ s) :
    ∀ q ∈ listPoints X δ, distToList S q (listPoints A γ) ≤ r + 2 * s + L := by
  intro q hq
  obtain ⟨m, hm, rfl⟩ := exists_index_of_mem_listPoints hq
  have hP : listPoints A γ ≠ [] := listPoints_ne_nil A γ
  have hδletters : ∀ x ∈ δ, x ∈ S := hδ.isWord.letters
  by_contra hcon
  have hfar_m : r + 2 * s + L < distToList S (X * (δ.take m).prod) (listPoints A γ) :=
    not_le.mp hcon
  have hm_lt : m < δ.length := by
    rcases lt_or_eq_of_le hm with h | h
    · exact h
    · rw [h, List.take_length] at hfar_m
      omega
  -- the last exit `g` before `m`
  have hδm : IsGeodesicWord S (δ.take m) (δ.take m).prod := isGeodesicWord_take hS hδ m
  obtain ⟨g, hg_le, hg_eq, hg_far⟩ := exists_exit_index hS hP hδm hstart
    (show r ≤ distToList S (X * (δ.take m).prod) (listPoints A γ) by omega)
  have hlenm : (δ.take m).length = m := by
    rw [List.length_take]
    omega
  rw [hlenm] at hg_le
  have hg_far' : ∀ t, g ≤ t → t ≤ m →
      r ≤ distToList S (X * (δ.take t).prod) (listPoints A γ) := by
    intro t hgt htm
    have h := hg_far t hgt
    rwa [List.take_take, min_eq_left htm] at h
  have hg_eq' : distToList S (X * (δ.take g).prod) (listPoints A γ) = r := by
    rwa [List.take_take, min_eq_left hg_le] at hg_eq
  have hmg : wordDist S (X * (δ.take m).prod) (X * (δ.take g).prod) = m - g := by
    rw [wordDist_comm hS, wordDist_take_of_geodesic hS hδ X hg_le hm]
  have hlip := distToList_le_add_wordDist hS hP (X * (δ.take m).prod) (X * (δ.take g).prod)
  have hlong : 2 * s + L < m - g := by omega
  -- the stretch from `g` to `m`
  have hβ₁letters : ∀ x ∈ (δ.drop g).take (m - g), x ∈ S :=
    fun x hx => hδletters x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  have hsplitm : δ.take m = δ.take g ++ (δ.drop g).take (m - g) := by
    rw [← List.take_add]
    congr 1
    omega
  have hβ₁prod : X * (δ.take g).prod * ((δ.drop g).take (m - g)).prod =
      X * (δ.take m).prod := by
    rw [hsplitm, List.prod_append, mul_assoc]
  have hβ₁far : ∀ q ∈ listPoints (X * (δ.take g).prod) ((δ.drop g).take (m - g)),
      r ≤ distToList S q (listPoints A γ) := by
    intro q hq
    obtain ⟨j, hgj, hjm, rfl⟩ := exists_index_of_mem_listPoints_drop_take hq
    exact hg_far' j hgj (by omega)
  by_cases hexb : ∃ b, m < b ∧ b ≤ δ.length ∧
      distToList S (X * (δ.take b).prod) (listPoints A γ) ≤ r
  · -- the next entry along `δ`
    obtain ⟨b, hmb, hbl, hbd⟩ := hexb
    have hω₂ : IsGeodesicWord S ((δ.drop m).take (b - m)) ((δ.drop m).take (b - m)).prod :=
      isGeodesicWord_take hS (isGeodesicWord_drop hS hδ m) (b - m)
    have hsplitb : δ.take b = δ.take m ++ (δ.drop m).take (b - m) := by
      rw [← List.take_add]
      congr 1
      omega
    have hω₂prod : X * (δ.take m).prod * ((δ.drop m).take (b - m)).prod =
        X * (δ.take b).prod := by
      rw [hsplitb, List.prod_append, mul_assoc]
    obtain ⟨n, hn_le, hn_eq, hn_far⟩ := exists_entry_index hS hP hω₂
      (P := X * (δ.take m).prod) (by omega) (by rw [hω₂prod]; exact hbd)
    have hlenb : ((δ.drop m).take (b - m)).length = b - m := by
      rw [List.length_take, List.length_drop]
      omega
    rw [hlenb] at hn_le
    have hβ₂prod : X * (δ.take m).prod * (((δ.drop m).take (b - m)).take n).prod =
        X * (δ.take (m + n)).prod := by
      rw [List.take_take, min_eq_left hn_le, List.take_add, List.prod_append, mul_assoc]
    have hH := three_mul_wordDist_le_of_bowditchH4_append hH4 hγ
      (X := X * (δ.take g).prod) (β₁ := (δ.drop g).take (m - g))
      (β₂ := ((δ.drop m).take (b - m)).take n) hβ₁letters
      (fun x hx => hδletters x (List.mem_of_mem_drop
        (List.mem_of_mem_take (List.mem_of_mem_take hx))))
      hg_eq' (by rw [hβ₁prod]; exact hn_eq) hβ₁far
      (by
        rw [hβ₁prod]
        intro q hq
        obtain ⟨j, hjn, rfl⟩ := exists_index_of_mem_listPoints_take hq
        exact hn_far j hjn)
    rw [hβ₁prod, hβ₂prod] at hH
    simp only [List.length_take, List.length_drop] at hH
    have hgm : wordDist S (X * (δ.take g).prod) (X * (δ.take (m + n)).prod) = m + n - g :=
      wordDist_take_of_geodesic hS hδ X (by omega) (by omega)
    omega
  · -- no entry along `δ`: continue along a shortest path to `γ`
    have hfar_after : ∀ t, m < t → t ≤ δ.length →
        r < distToList S (X * (δ.take t).prod) (listPoints A γ) :=
      fun t hmt htl => not_le.mp (fun h => hexb ⟨t, hmt, htl, h⟩)
    have hPfar : r < distToList S (X * δ.prod) (listPoints A γ) := by
      have h := hfar_after δ.length hm_lt le_rfl
      rwa [List.take_length] at h
    obtain ⟨P'', hP''mem, hP''d⟩ := exists_mem_distToList_eq S (X * δ.prod) hP
    obtain ⟨ν, hν⟩ := exists_isGeodesicWord hS ((X * δ.prod)⁻¹ * P'')
    have hνletters : ∀ x ∈ ν, x ∈ S := hν.isWord.letters
    have hνgeo : IsGeodesicWord S ν ν.prod := by
      refine ⟨⟨hνletters, rfl⟩, ?_⟩
      rw [hν.isWord.prod_eq]
      exact hν.length_eq
    have hνprod : X * δ.prod * ν.prod = P'' := by
      rw [hν.isWord.prod_eq]
      group
    have hνlen : ν.length = wordDist S (X * δ.prod) P'' := hν.length_eq
    obtain ⟨n, hn_le, hn_eq, hn_far⟩ := exists_entry_index hS hP hνgeo (P := X * δ.prod)
      hPfar.le (by rw [hνprod, distToList_eq_zero_of_mem S hP''mem]; exact Nat.zero_le _)
    have hβ₁'prod : X * (δ.take g).prod * (δ.drop g).prod = X * δ.prod := by
      rw [mul_assoc, ← List.prod_append, List.take_append_drop]
    have hH := three_mul_wordDist_le_of_bowditchH4_append hH4 hγ
      (X := X * (δ.take g).prod) (β₁ := δ.drop g) (β₂ := ν.take n)
      (fun x hx => hδletters x (List.mem_of_mem_drop hx))
      (fun x hx => hνletters x (List.mem_of_mem_take hx))
      hg_eq' (by rw [hβ₁'prod]; exact hn_eq)
      (by
        intro q hq
        obtain ⟨j, hgj, rfl⟩ := exists_index_of_mem_listPoints_drop hq
        by_cases hjm : j ≤ m
        · exact hg_far' j hgj hjm
        · by_cases hjl : j ≤ δ.length
          · exact (hfar_after j (by omega) hjl).le
          · rw [List.take_of_length_le (by omega)]
            exact hPfar.le)
      (by
        rw [hβ₁'prod]
        intro q hq
        obtain ⟨j, hjn, rfl⟩ := exists_index_of_mem_listPoints_take hq
        exact hn_far j hjn)
    rw [hβ₁'prod] at hH
    simp only [List.length_take, List.length_drop] at hH
    have hgP : wordDist S (X * (δ.take g).prod) (X * δ.prod) = δ.length - g := by
      have h := wordDist_take_of_geodesic hS hδ X (show g ≤ δ.length by omega) le_rfl
      rwa [List.take_length] at h
    have hPE : wordDist S (X * δ.prod) (X * δ.prod * (ν.take n).prod) ≤ ν.length :=
      wordDist_start_le_of_mem hνletters (take_mem_listPoints _ ν n)
    have ht := wordDist_triangle hS (X * (δ.take g).prod) (X * δ.prod * (ν.take n).prod)
      (X * δ.prod)
    have hc := wordDist_comm hS (X * δ.prod * (ν.take n).prod) (X * δ.prod)
    omega

/-! ## Betweenness -/

/-- A vertex of a geodesic word lies between its endpoints. -/
theorem isBetween_of_mem_listPoints {S : Set Q} (hS : IsSymmetricGeneratingSet S) {X : Q}
    {γ : List Q} (hγ : IsGeodesicWord S γ γ.prod) {q : Q} (hq : q ∈ listPoints X γ) :
    Hyperbolic.IsBetween S X q (X * γ.prod) := by
  obtain ⟨i, hi, rfl⟩ := exists_index_of_mem_listPoints hq
  have h1 := wordDist_take_of_geodesic hS hγ X (Nat.zero_le i) hi
  have h2 := wordDist_take_of_geodesic hS hγ X hi le_rfl
  have h3 := wordDist_take_of_geodesic hS hγ X (Nat.zero_le γ.length) le_rfl
  simp only [List.take_zero, List.prod_nil, mul_one, List.take_length] at h1 h2 h3
  unfold Hyperbolic.IsBetween
  omega

/-- Betweenness is symmetric in the endpoints. -/
theorem isBetween_symm {S : Set Q} (hS : IsSymmetricGeneratingSet S) {b p c : Q}
    (h : Hyperbolic.IsBetween S b p c) : Hyperbolic.IsBetween S c p b := by
  unfold Hyperbolic.IsBetween at h ⊢
  have h1 := wordDist_comm hS b p
  have h2 := wordDist_comm hS p c
  have h3 := wordDist_comm hS b c
  omega

/-- A point between `x` and `y` is a vertex of some geodesic word from `x` to `y`. -/
theorem exists_geodesic_through_of_isBetween {S : Set Q} (hS : IsSymmetricGeneratingSet S)
    {x p y : Q} (h : Hyperbolic.IsBetween S x p y) :
    ∃ γ : List Q, IsGeodesicWord S γ γ.prod ∧ x * γ.prod = y ∧ p ∈ listPoints x γ := by
  obtain ⟨σ₁, hσ₁⟩ := exists_isGeodesicWord hS (x⁻¹ * p)
  obtain ⟨σ₂, hσ₂⟩ := exists_isGeodesicWord hS (p⁻¹ * y)
  have hprod : (σ₁ ++ σ₂).prod = x⁻¹ * y := by
    rw [List.prod_append, hσ₁.isWord.prod_eq, hσ₂.isWord.prod_eq]
    group
  refine ⟨σ₁ ++ σ₂, ⟨⟨?_, rfl⟩, ?_⟩, ?_, ?_⟩
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hσ₁.isWord.letters z hz
    · exact hσ₂.isWord.letters z hz
  · rw [List.length_append, hσ₁.length_eq, hσ₂.length_eq, hprod]
    exact h
  · rw [hprod]
    group
  · rw [mem_listPoints_append]
    left
    have e : p = x * σ₁.prod := by
      rw [hσ₁.isWord.prod_eq]
      group
    rw [e]
    exact end_mem_listPoints x σ₁

/-! ## Slim triangles -/

/-- **Bowditch's Proposition 6.2.4 in the Cayley graph.**  If the word metric of a
symmetric generating set is `(r, L)`-H4 with `r > 0`, its geodesic triangles are slim,
at constant `r + 4 M + L` with `M = 10 (4 r + L) + L`. -/
theorem isSlimTriangles_of_bowditchH4 {S : Set Q} (hS : IsSymmetricGeneratingSet S)
    {r L : ℕ} (hr : 0 < r) (hH4 : BowditchH4 S r L) :
    Hyperbolic.IsSlimTriangles S (r + 4 * (10 * (4 * r + L) + L) + L) := by
  intro x y z p hp
  obtain ⟨γ₁, hγ₁, h₁₂, hpγ₁⟩ := exists_geodesic_through_of_isBetween hS hp
  obtain ⟨γ₂, hγ₂'⟩ := exists_isGeodesicWord hS (y⁻¹ * z)
  obtain ⟨γ₃, hγ₃'⟩ := exists_isGeodesicWord hS (z⁻¹ * x)
  have hγ₂ : IsGeodesicWord S γ₂ γ₂.prod := by
    refine ⟨⟨hγ₂'.isWord.letters, rfl⟩, ?_⟩
    rw [hγ₂'.isWord.prod_eq]
    exact hγ₂'.length_eq
  have hγ₃ : IsGeodesicWord S γ₃ γ₃.prod := by
    refine ⟨⟨hγ₃'.isWord.letters, rfl⟩, ?_⟩
    rw [hγ₃'.isWord.prod_eq]
    exact hγ₃'.length_eq
  have h₂₃ : y * γ₂.prod = z := by
    rw [hγ₂'.isWord.prod_eq]
    group
  have h₃₁ : z * γ₃.prod = x := by
    rw [hγ₃'.isWord.prod_eq]
    group
  obtain ⟨W, hW⟩ := exists_centre_of_bowditchH4 hS hr hH4 hγ₁ hγ₂ hγ₃ h₁₂ h₂₃ h₃₁
  have hM₁ := hW.near₁
  have hM₂ := hW.near₂
  have hM₃ := hW.near₃
  obtain ⟨W₁, hW₁mem, hW₁d⟩ := exists_mem_distToList_eq S W (listPoints_ne_nil x γ₁)
  obtain ⟨W₂, hW₂mem, hW₂d⟩ := exists_mem_distToList_eq S W (listPoints_ne_nil y γ₂)
  obtain ⟨W₃, hW₃mem, hW₃d⟩ := exists_mem_distToList_eq S W (listPoints_ne_nil z γ₃)
  obtain ⟨w, _hw, rfl⟩ := exists_index_of_mem_listPoints hW₁mem
  obtain ⟨i, _hi, rfl⟩ := exists_index_of_mem_listPoints hpγ₁
  by_cases hiw : i ≤ w
  · -- `p` is on the piece of `[x, y]` before `W₁`, which fellow travels `[z, x]`
    have hx : distToList S x (listPoints z γ₃) ≤ r := by
      have hmem : x ∈ listPoints z γ₃ := by
        rw [← h₃₁]
        exact end_mem_listPoints z γ₃
      rw [distToList_eq_zero_of_mem S hmem]
      exact Nat.zero_le _
    have hW₁ : distToList S (x * (γ₁.take w).prod) (listPoints z γ₃) ≤
        2 * (10 * (4 * r + L) + L) := by
      have h1 := distToList_le_of_mem S (x * (γ₁.take w).prod) hW₃mem
      have h2 := wordDist_triangle hS (x * (γ₁.take w).prod) W W₃
      have h3 := wordDist_comm hS (x * (γ₁.take w).prod) W
      omega
    have hmem : x * (γ₁.take i).prod ∈ listPoints x (γ₁.take w) := by
      rw [mem_listPoints_iff]
      exact ⟨i, by rw [List.take_take, min_eq_left hiw]⟩
    have hft := distToList_le_of_bowditchH4_of_end hS hH4 hγ₃ (isGeodesicWord_take hS hγ₁ w)
      hx hW₁ _ hmem
    obtain ⟨q, hqmem, hqd⟩ := exists_mem_distToList_eq S (x * (γ₁.take i).prod)
      (listPoints_ne_nil z γ₃)
    refine Or.inl ⟨q, ?_, by omega⟩
    have hb := isBetween_of_mem_listPoints hS hγ₃ hqmem
    rw [h₃₁] at hb
    exact isBetween_symm hS hb
  · -- `p` is on the piece after `W₁`, which read backwards fellow travels `[y, z]`
    have hwi : w ≤ i := (not_le.mp hiw).le
    have hy : x * (γ₁.take w).prod * (γ₁.drop w).prod = y := by
      rw [mul_assoc, ← List.prod_append, List.take_append_drop, h₁₂]
    have hyW₁ : y * (revList (γ₁.drop w)).prod = x * (γ₁.take w).prod := by
      rw [prod_revList, ← hy]
      group
    have hystart : distToList S y (listPoints y γ₂) ≤ r := by
      rw [distToList_eq_zero_of_mem S (start_mem_listPoints y γ₂)]
      exact Nat.zero_le _
    have hW₁ : distToList S (y * (revList (γ₁.drop w)).prod) (listPoints y γ₂) ≤
        2 * (10 * (4 * r + L) + L) := by
      rw [hyW₁]
      have h1 := distToList_le_of_mem S (x * (γ₁.take w).prod) hW₂mem
      have h2 := wordDist_triangle hS (x * (γ₁.take w).prod) W W₂
      have h3 := wordDist_comm hS (x * (γ₁.take w).prod) W
      omega
    have hmem : x * (γ₁.take i).prod ∈ listPoints y (revList (γ₁.drop w)) := by
      rw [← hy, mem_listPoints_revList, mem_listPoints_iff]
      refine ⟨i - w, ?_⟩
      have e : w + (i - w) = i := by omega
      rw [mul_assoc, ← List.prod_append, ← List.take_add, e]
    have hft := distToList_le_of_bowditchH4_of_end hS hH4 hγ₂
      (isGeodesicWord_revList hS (isGeodesicWord_drop hS hγ₁ w)) hystart hW₁ _ hmem
    obtain ⟨q, hqmem, hqd⟩ := exists_mem_distToList_eq S (x * (γ₁.take i).prod)
      (listPoints_ne_nil y γ₂)
    refine Or.inr ⟨q, ?_, by omega⟩
    have hb := isBetween_of_mem_listPoints hS hγ₂ hqmem
    rw [h₂₃] at hb
    exact isBetween_symm hS hb

end DiscreteStokes
end GroupApproximation

#audit_axioms GroupApproximation.DiscreteStokes.exists_entry_index
#audit_axioms GroupApproximation.DiscreteStokes.three_mul_wordDist_le_of_bowditchH4_append
#audit_axioms GroupApproximation.DiscreteStokes.distToList_le_of_bowditchH4_of_end
#audit_axioms GroupApproximation.DiscreteStokes.isBetween_of_mem_listPoints
#audit_axioms GroupApproximation.DiscreteStokes.exists_geodesic_through_of_isBetween
#audit_axioms GroupApproximation.DiscreteStokes.isSlimTriangles_of_bowditchH4
