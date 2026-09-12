import GroupApproximation.Algebra.CayleyPathVertices

/-!
# Bowditch's detour property H4 from the linear Stokes inequality

Bowditch (*Notes on Gromov's hyperbolicity criterion for path-metric spaces*,
Definition 4) calls a geodesic space `(r, L)`-H4 when every path joining two points
at distance exactly `r` from a geodesic segment, and staying at distance at least
`r` from it, has length at least `3 d(X, Y) - L`.  His Proposition 6.2.4 turns H4
into thin triangles by a purely metric argument.

This module derives H4 in a Cayley graph from `DiscreteStokes.LinearStokes S C`,
with `r = 3 C + 1` and `L = 15 r`.  Close the detour `β` from `X` to `Y` into a loop
through the nearest points `X'`, `Y'` of the geodesic: a geodesic word of length
`r` from `X'` to `X`, the detour, a geodesic word of length `r` from `Y` to `Y'`,
and the segment of the geodesic from `Y'` back to `X'`, read backwards when `X'`
comes first.  The detour is at distance at least `r` from that segment, and the two
connecting words are at distance at least `d(X', Y') - 2 r` from each other, so the
quadrangle bound (`two_mul_mul_le_of_linearStokes`) gives
`2 r (d(X', Y') - 2 r) ≤ C × length`.  With `r = 3 C + 1` that forces
`3 d(X', Y') ≤ |β| + 9 r`, and `d(X, Y) ≤ d(X', Y') + 2 r` finishes.
-/

namespace GroupApproximation
namespace DiscreteStokes

open WordMetric

universe v

variable {Q : Type v} [Group Q]

/-- **Bowditch's `(r, L)`-H4 in the Cayley graph.**  A path `β` from `X` whose
vertices all stay at distance at least `r` from the vertices of a geodesic word `γ`
read from `A`, with both endpoints at distance exactly `r` from it, has length at
least `3 d(X, X β) - L`. -/
def BowditchH4 (S : Set Q) (r L : ℕ) : Prop :=
  ∀ (A : Q) (γ : List Q), IsGeodesicWord S γ γ.prod →
    ∀ (X : Q) (β : List Q), (∀ x ∈ β, x ∈ S) →
      distToList S X (listPoints A γ) = r →
      distToList S (X * β.prod) (listPoints A γ) = r →
      (∀ q ∈ listPoints X β, r ≤ distToList S q (listPoints A γ)) →
        3 * wordDist S X (X * β.prod) ≤ β.length + L

/-- **The detour estimate.**  The loop `σ g₁ β g₂` read from `Y'`, where `σ` runs
inside the vertex list `P` from `Y'` to `X'` along a shortest route, `g₁` is a word of
length `r = 3 C + 1` from `X'` to `X`, `β` avoids the `r`-neighbourhood of `P`, and
`g₂` is a word of length `r` from `X β` back to `Y'`. -/
theorem three_mul_wordDist_le_of_detour {S : Set Q} (hS : IsSymmetricGeneratingSet S)
    {C : ℕ} (hC : LinearStokes S C) {P : List Q} {X X' Y' : Q} {β σ g₁ g₂ : List Q}
    (hβ : ∀ x ∈ β, x ∈ S) (hσ : ∀ x ∈ σ, x ∈ S) (hg₁ : ∀ x ∈ g₁, x ∈ S)
    (hg₂ : ∀ x ∈ g₂, x ∈ S)
    (hσprod : Y' * σ.prod = X') (hσlen : σ.length = wordDist S Y' X')
    (hσP : ∀ q ∈ listPoints Y' σ, q ∈ P)
    (hg₁prod : X' * g₁.prod = X) (hg₁len : g₁.length = 3 * C + 1)
    (hg₂prod : X * β.prod * g₂.prod = Y') (hg₂len : g₂.length = 3 * C + 1)
    (havoid : ∀ q ∈ listPoints X β, 3 * C + 1 ≤ distToList S q P) :
    3 * wordDist S X (X * β.prod) ≤ β.length + 15 * (3 * C + 1) := by
  have hl : ∀ x ∈ σ ++ g₁ ++ β ++ g₂, x ∈ S := by
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with ((hx | hx) | hx) | hx
    · exact hσ x hx
    · exact hg₁ x hx
    · exact hβ x hx
    · exact hg₂ x hx
  have hclosed : (σ ++ g₁ ++ β ++ g₂).prod = 1 := by
    have e₁ : σ.prod = Y'⁻¹ * X' := by
      rw [← hσprod]
      group
    have e₂ : g₁.prod = X'⁻¹ * X := by
      rw [← hg₁prod]
      group
    have e₃ : g₂.prod = (X * β.prod)⁻¹ * Y' := by
      rw [← hg₂prod]
      group
    simp only [List.prod_append]
    rw [e₁, e₂, e₃]
    group
  have hbase₃ : Y' * (σ ++ g₁).prod = X := by
    rw [List.prod_append, ← mul_assoc, hσprod, hg₁prod]
  have hsep₁ : ∀ q ∈ listPoints (Y' * (σ ++ g₁).prod) β,
      3 * C + 1 ≤ distToList S q (listPoints Y' σ) := by
    intro q hq
    rw [hbase₃] at hq
    exact le_distToList S q (listPoints_ne_nil _ _)
      (fun p hp => le_trans (havoid q hq) (distToList_le_of_mem S q (hσP p hp)))
  have hbase₄ : Y' * (σ ++ g₁ ++ β).prod = X * β.prod := by
    rw [List.prod_append, List.prod_append, ← mul_assoc, ← mul_assoc, hσprod, hg₁prod]
  have hsep₂ : ∀ q ∈ listPoints (Y' * (σ ++ g₁ ++ β).prod) g₂,
      wordDist S Y' X' - 2 * (3 * C + 1) ≤ distToList S q (listPoints (Y' * σ.prod) g₁) := by
    intro q hq
    rw [hbase₄] at hq
    rw [hσprod]
    apply le_distToList S q (listPoints_ne_nil _ _)
    intro p hp
    have hqY : wordDist S q Y' ≤ 3 * C + 1 := by
      have h := wordDist_end_le_of_mem hg₂ hq
      rwa [hg₂prod, hg₂len] at h
    have hpX : wordDist S X' p ≤ 3 * C + 1 := by
      have h := wordDist_start_le_of_mem hg₁ hp
      rwa [hg₁len] at h
    have ht₁ := wordDist_triangle hS Y' q X'
    have ht₂ := wordDist_triangle hS q p X'
    have hc₁ := wordDist_comm hS Y' q
    have hc₂ := wordDist_comm hS p X'
    omega
  have hquad := two_mul_mul_le_of_linearStokes hS hC Y' σ g₁ β g₂ hl hclosed (3 * C + 1)
    (wordDist S Y' X' - 2 * (3 * C + 1)) hsep₁ hsep₂
  simp only [List.length_append] at hquad
  rw [hσlen, hg₁len, hg₂len] at hquad
  have hXX' : wordDist S X X' ≤ 3 * C + 1 := by
    have h := wordDist_end_le_of_mem hg₁ (start_mem_listPoints X' g₁)
    rw [hg₁prod, hg₁len] at h
    rw [wordDist_comm hS]
    exact h
  have hYY' : wordDist S (X * β.prod) Y' ≤ 3 * C + 1 := by
    have h := wordDist_end_le_of_mem hg₂ (start_mem_listPoints (X * β.prod) g₂)
    rwa [hg₂prod, hg₂len] at h
  have ht₃ := wordDist_triangle hS X X' (X * β.prod)
  have ht₄ := wordDist_triangle hS X' Y' (X * β.prod)
  have hc₃ := wordDist_comm hS X' Y'
  have hc₄ := wordDist_comm hS Y' (X * β.prod)
  have hdist : wordDist S X (X * β.prod) ≤ wordDist S Y' X' + 2 * (3 * C + 1) := by omega
  by_cases hD2 : wordDist S Y' X' < 2 * (3 * C + 1)
  · omega
  · have hle : 2 * (3 * C + 1) ≤ wordDist S Y' X' := not_lt.mp hD2
    have hcast : ((wordDist S Y' X' - 2 * (3 * C + 1) : ℕ) : ℤ) =
        (wordDist S Y' X' : ℤ) - 2 * (3 * C + 1) := by
      rw [Nat.cast_sub hle]
      push_cast
      ring
    rw [hcast] at hquad
    push_cast at hquad
    have hC0 : (0 : ℤ) ≤ C := Nat.cast_nonneg C
    have hB0 : (0 : ℤ) ≤ β.length := Nat.cast_nonneg _
    have key : (5 * (C : ℤ) + 2) * (3 * (wordDist S Y' X' : ℤ)) ≤
        (5 * (C : ℤ) + 2) * ((β.length : ℤ) + 27 * C + 9) := by
      nlinarith [hquad, mul_nonneg hC0 hB0, sq_nonneg (C : ℤ)]
    have hpos : (0 : ℤ) < 5 * C + 2 := by positivity
    have h3 : 3 * (wordDist S Y' X' : ℤ) ≤ (β.length : ℤ) + 27 * C + 9 :=
      le_of_mul_le_mul_left key hpos
    have h3' : 3 * wordDist S Y' X' ≤ β.length + 27 * C + 9 := by exact_mod_cast h3
    omega

/-- **The linear Stokes inequality gives Bowditch's H4**, at `r = 3 C + 1` and
`L = 15 r`. -/
theorem bowditchH4_of_linearStokes {S : Set Q} (hS : IsSymmetricGeneratingSet S) {C : ℕ}
    (hC : LinearStokes S C) : BowditchH4 S (3 * C + 1) (15 * (3 * C + 1)) := by
  intro A γ hγ X β hβ hXd hYd havoid
  obtain ⟨X', hX'mem, hX'd⟩ := exists_mem_distToList_eq S X (listPoints_ne_nil A γ)
  obtain ⟨Y', hY'mem, hY'd⟩ :=
    exists_mem_distToList_eq S (X * β.prod) (listPoints_ne_nil A γ)
  rw [hXd] at hX'd
  rw [hYd] at hY'd
  obtain ⟨i, hi, rfl⟩ := exists_index_of_mem_listPoints hX'mem
  obtain ⟨j, hj, rfl⟩ := exists_index_of_mem_listPoints hY'mem
  obtain ⟨g₁, hg₁⟩ := exists_isGeodesicWord hS ((A * (γ.take i).prod)⁻¹ * X)
  obtain ⟨g₂, hg₂⟩ := exists_isGeodesicWord hS ((X * β.prod)⁻¹ * (A * (γ.take j).prod))
  have hg₁prod : A * (γ.take i).prod * g₁.prod = X := by
    rw [hg₁.isWord.prod_eq]
    group
  have hg₁len : g₁.length = 3 * C + 1 := by
    rw [hg₁.length_eq]
    change wordDist S (A * (γ.take i).prod) X = _
    rw [wordDist_comm hS]
    exact hX'd
  have hg₂prod : X * β.prod * g₂.prod = A * (γ.take j).prod := by
    rw [hg₂.isWord.prod_eq]
    group
  have hg₂len : g₂.length = 3 * C + 1 := by
    rw [hg₂.length_eq]
    exact hY'd
  have hγletters : ∀ x ∈ γ, x ∈ S := hγ.isWord.letters
  rcases le_total j i with hji | hij
  · have hsplit : γ.take i = γ.take j ++ (γ.drop j).take (i - j) := by
      rw [← List.take_add]
      congr 1
      omega
    refine three_mul_wordDist_le_of_detour hS hC (P := listPoints A γ)
      (σ := (γ.drop j).take (i - j)) hβ ?_ hg₁.isWord.letters hg₂.isWord.letters ?_ ?_ ?_
      hg₁prod hg₁len hg₂prod hg₂len havoid
    · intro x hx
      exact hγletters x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
    · rw [hsplit, List.prod_append, mul_assoc]
    · rw [wordDist_take_of_geodesic hS hγ A hji hi, List.length_take, List.length_drop]
      omega
    · intro q hq
      exact mem_listPoints_of_mem_drop_take hq
  · have hsplit : γ.take j = γ.take i ++ (γ.drop i).take (j - i) := by
      rw [← List.take_add]
      congr 1
      omega
    have hY'eq : A * (γ.take j).prod = A * (γ.take i).prod * ((γ.drop i).take (j - i)).prod := by
      rw [hsplit, List.prod_append, mul_assoc]
    refine three_mul_wordDist_le_of_detour hS hC (P := listPoints A γ)
      (σ := revList ((γ.drop i).take (j - i))) hβ ?_ hg₁.isWord.letters hg₂.isWord.letters
      ?_ ?_ ?_ hg₁prod hg₁len hg₂prod hg₂len havoid
    · exact letters_revList hS
        (fun x hx => hγletters x (List.mem_of_mem_drop (List.mem_of_mem_take hx)))
    · rw [prod_revList, hY'eq]
      group
    · rw [length_revList, wordDist_comm hS, wordDist_take_of_geodesic hS hγ A hij hj,
        List.length_take, List.length_drop]
      omega
    · intro q hq
      rw [hY'eq, mem_listPoints_revList] at hq
      exact mem_listPoints_of_mem_drop_take hq

end DiscreteStokes
end GroupApproximation

#audit_axioms GroupApproximation.DiscreteStokes.three_mul_wordDist_le_of_detour
#audit_axioms GroupApproximation.DiscreteStokes.bowditchH4_of_linearStokes
