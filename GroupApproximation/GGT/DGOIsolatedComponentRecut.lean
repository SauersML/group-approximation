import GroupApproximation.GGT.OsinTheorem54SepPolygon

/-!
# Making an isolated component a side, at the cost of two sides

Dahmani--Guirardel--Osin prove their §4.2 bound for a component that *is a side*
of the polygon (their Lemma 4.16 normalises the distinguished component to the
first side before anything else happens).  Osin's Lemma 4.2, which is what
`OsinComponents.IsolatedComponentBound` states, allows the isolated component to
sit anywhere.  This module is the transfer between the two shapes: cutting the
side that carries the component at both ends of the component turns an `n`-gon
into an `(n+2)`-gon in which the component is a side, and nothing else changes ---
same word, same basepoint, same component, same span.

Concept grep before writing: `side`, `cut function`, `corner` in
`OsinTheorem54SepPolygon`, `OsinTheorem54SepFourGon*`, `DGOPolygonGeodesicChain`.
What exists is `GeodesicFourGon` (osin-24), which *carries* a cut function for a
4-gon, and `GeodesicFourGon.isComp_side_succ`, which says a component that is
already a side of a `(1,0)`-gon is a single letter.  No module refines a cut
function, and no module produces a polygon with a prescribed side.

## The shape of the statement

The polygon data is taken apart rather than packaged: the cut function has to be
named, because "the component lies inside side `t`" is a statement about it, and
`IsQuasiGeodesicPolygon` binds it existentially.  A consumer holding a polygon
opens that existential itself and locates `t`.  The refined cut function is

    c' s = if s ≤ t then c s else if s ≤ t+1 then i else if s ≤ t+2 then k
             else c (s-2) ,

so the sides of the new polygon are those of the old one with side `t` replaced
by `[c t, i]`, `[i, k]`, `[k, c (t+1)]`.  Every one of them is an interval inside
a single old side, which is why the quasi-geodesic clause transfers verbatim
(`sub_side_of_recut`): no metric input is needed, only monotonicity.

## What is *not* covered, and why it needs the normalisation

The hypothesis `c t ≤ i` and `k ≤ c (t+1)` --- the component lies inside one side
--- cannot be dropped.  A maximal run may straddle a corner, and then the side
`[i,k]` of the refined polygon is not quasi-geodesic: all of a run's vertices lie
in one coset of `H lam`, so any two of them are one letter apart
(`wordDist_vertex_le_one_of_mem_comp`), and the clause for that side would demand
`(k - i)/μ - b ≤ 1`.  At `(μ,b) = (1,0)` this is sharp rather than pessimistic: a
run straddling one corner has at most one letter on each side of it, hence may
have two, and `2 ≤ 1` is false.  The straddling case is exactly what the run to
single-letter normalisation is for; it is not repaired here.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The refined cut function -/

/-- **Every side of the refined polygon lies inside a side of the old one.**

The refinement inserts `i` and `k` after the corner `t`, so the sides are the old
sides with side `t` split into three.  This is the whole geometric content of the
recut: it is proved from `c t ≤ i ≤ k ≤ c (t+1)` alone, with no monotonicity and
no metric input, and it is what lets the quasi-geodesic clause be quoted
unchanged. -/
theorem sub_side_of_recut {c : ℕ → ℕ} {n t i k : ℕ} (ht : t < n) (hti : c t ≤ i)
    (hik : i ≤ k) (hkt : k ≤ c (t + 1)) {s : ℕ} (hs : s < n + 2) :
    ∃ s₀ : ℕ, s₀ < n ∧
      c s₀ ≤ (if s ≤ t then c s else if s ≤ t + 1 then i
        else if s ≤ t + 2 then k else c (s - 2)) ∧
      (if s + 1 ≤ t then c (s + 1) else if s + 1 ≤ t + 1 then i
        else if s + 1 ≤ t + 2 then k else c (s + 1 - 2)) ≤ c (s₀ + 1) := by
  by_cases h1 : s + 1 ≤ t
  · exact ⟨s, by omega, le_of_eq (by rw [if_pos (show s ≤ t by omega)]),
      le_of_eq (by rw [if_pos h1])⟩
  · by_cases h2 : s ≤ t
    · -- `s = t`: the side `[c t, i]`
      refine ⟨t, ht, le_of_eq ?_, ?_⟩
      · rw [if_pos h2, show s = t from by omega]
      · rw [if_neg h1, if_pos (show s + 1 ≤ t + 1 by omega)]
        omega
    · by_cases h3 : s ≤ t + 1
      · -- `s = t + 1`: the side `[i, k]`, the component itself
        refine ⟨t, ht, ?_, ?_⟩
        · rw [if_neg h2, if_pos h3]
          exact hti
        · rw [if_neg (show ¬ s + 1 ≤ t by omega),
            if_neg (show ¬ s + 1 ≤ t + 1 by omega),
            if_pos (show s + 1 ≤ t + 2 by omega)]
          exact hkt
      · by_cases h4 : s ≤ t + 2
        · -- `s = t + 2`: the side `[k, c (t+1)]`
          refine ⟨t, ht, ?_, le_of_eq ?_⟩
          · rw [if_neg h2, if_neg h3, if_pos h4]
            omega
          · rw [if_neg (show ¬ s + 1 ≤ t by omega),
              if_neg (show ¬ s + 1 ≤ t + 1 by omega),
              if_neg (show ¬ s + 1 ≤ t + 2 by omega),
              show s + 1 - 2 = t + 1 from by omega]
        · -- an old side, shifted by two
          refine ⟨s - 2, by omega, le_of_eq ?_, le_of_eq ?_⟩
          · rw [if_neg h2, if_neg h3, if_neg h4]
          · rw [if_neg (show ¬ s + 1 ≤ t by omega),
              if_neg (show ¬ s + 1 ≤ t + 1 by omega),
              if_neg (show ¬ s + 1 ≤ t + 2 by omega),
              show s + 1 - 2 = s - 2 + 1 from by omega]

/-! ## The transfer -/

/-- **Osin's Lemma 4.2 form follows from Dahmani--Guirardel--Osin's side form.**

The first binder is the side form of the `§4.2` bound at `N ≤ 6` sides: for a
`(μ,b)`-quasi-geodesic `N`-gon whose cut function is named, an isolated component
that *is* the side `t` has its span in `D.relBall lam (C * N)`.  Everything after
it is proved: for a component lying inside side `t` of an `n`-gon with `n ≤ 4`,
the span lies in `D.relBall lam (C * (n + 2))`.

The polygon is taken apart into its clauses because the side hypothesis is a
statement about the cut function; a consumer holding
`IsQuasiGeodesicPolygon D mu b n v w` opens the existential and supplies `t`.

The hypothesis that the component lies inside one side is necessary; see the
module docstring for the straddling run that defeats the recut, and the run to
single-letter normalisation that repairs it. -/
theorem span_mem_relBall_of_sideForm (D : RelGenSet G Λ) (mu b : ℝ) (C : ℕ)
    (hside : ∀ (N : ℕ), N ≤ 6 → ∀ (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ),
      (∀ a ∈ w, D.IsLetter a) → RelLetter.listVal w = 1 → c 0 = 0 →
      c N = w.length → (∀ s : ℕ, c s ≤ c (s + 1)) →
      (∀ s : ℕ, s < N → ∀ p q : ℕ, c s ≤ p → p ≤ q → q ≤ c (s + 1) →
        ((q - p : ℕ) : ℝ) / mu - b
          ≤ ((wordDist D.alphabet.carrier (vertex v w p) (vertex v w q) : ℕ) : ℝ)) →
      ∀ (lam : Λ) (t : ℕ), t < N → IsComp lam w (c t) (c (t + 1)) →
        IsIsolated D.fam lam v w (c t) →
        (vertex v w (c t))⁻¹ * vertex v w (c (t + 1)) ∈ D.relBall lam (C * N))
    {n : ℕ} (hn : n ≤ 4) {v : G} {w : List (RelLetter G Λ)} {c : ℕ → ℕ}
    (hlet : ∀ a ∈ w, D.IsLetter a) (hclosed : RelLetter.listVal w = 1)
    (hc0 : c 0 = 0) (hcn : c n = w.length) (hcmono : ∀ s : ℕ, c s ≤ c (s + 1))
    (hcqg : ∀ s : ℕ, s < n → ∀ p q : ℕ, c s ≤ p → p ≤ q → q ≤ c (s + 1) →
      ((q - p : ℕ) : ℝ) / mu - b
        ≤ ((wordDist D.alphabet.carrier (vertex v w p) (vertex v w q) : ℕ) : ℝ))
    {lam : Λ} {i k t : ℕ} (ht : t < n) (hti : c t ≤ i) (hkt : k ≤ c (t + 1))
    (hcomp : IsComp lam w i k) (hiso : IsIsolated D.fam lam v w i) :
    (vertex v w i)⁻¹ * vertex v w k ∈ D.relBall lam (C * (n + 2)) := by
  have hik : i < k := hcomp.1
  set cc : ℕ → ℕ := fun s => if s ≤ t then c s else if s ≤ t + 1 then i
    else if s ≤ t + 2 then k else c (s - 2)
  have hccv : ∀ s : ℕ, cc s = if s ≤ t then c s else if s ≤ t + 1 then i
      else if s ≤ t + 2 then k else c (s - 2) := fun s => rfl
  have hccle : ∀ s : ℕ, s ≤ t → cc s = c s := by
    intro s hs
    rw [hccv s, if_pos hs]
  have hcc1 : cc (t + 1) = i := by
    rw [hccv, if_neg (show ¬ t + 1 ≤ t by omega), if_pos (le_refl (t + 1))]
  have hcc2 : cc (t + 2) = k := by
    rw [hccv, if_neg (show ¬ t + 2 ≤ t by omega),
      if_neg (show ¬ t + 2 ≤ t + 1 by omega), if_pos (le_refl (t + 2))]
  have hccge : ∀ s : ℕ, t + 3 ≤ s → cc s = c (s - 2) := by
    intro s hs
    rw [hccv s, if_neg (show ¬ s ≤ t by omega), if_neg (show ¬ s ≤ t + 1 by omega),
      if_neg (show ¬ s ≤ t + 2 by omega)]
  -- the refined cut function is a cut function
  have hcc0 : cc 0 = 0 := by
    rw [hccle 0 (Nat.zero_le t), hc0]
  have hccN : cc (n + 2) = w.length := by
    rw [hccge (n + 2) (by omega), show n + 2 - 2 = n from by omega, hcn]
  have hccmono : ∀ s : ℕ, cc s ≤ cc (s + 1) := by
    intro s
    rcases Nat.lt_or_ge (s + 1) (t + 1) with h1 | h1
    · rw [hccle s (by omega), hccle (s + 1) (by omega)]
      exact hcmono s
    · rcases Nat.lt_or_ge s (t + 1) with h2 | h2
      · rw [show s = t from by omega, hccle t le_rfl, hcc1]
        exact hti
      · rcases Nat.lt_or_ge s (t + 2) with h3 | h3
        · rw [show s = t + 1 from by omega, hcc1,
            show t + 1 + 1 = t + 2 from by omega, hcc2]
          exact le_of_lt hik
        · rcases Nat.lt_or_ge s (t + 3) with h4 | h4
          · rw [show s = t + 2 from by omega, hcc2,
              show t + 2 + 1 = t + 3 from by omega, hccge (t + 3) le_rfl,
              show t + 3 - 2 = t + 1 from by omega]
            exact hkt
          · rw [hccge s h4, hccge (s + 1) (by omega),
              show s + 1 - 2 = s - 2 + 1 from by omega]
            exact hcmono (s - 2)
  -- every refined side sits inside an old side, so the clause is quoted unchanged
  have hccqg : ∀ s : ℕ, s < n + 2 → ∀ p q : ℕ, cc s ≤ p → p ≤ q →
      q ≤ cc (s + 1) → ((q - p : ℕ) : ℝ) / mu - b
        ≤ ((wordDist D.alphabet.carrier (vertex v w p) (vertex v w q) : ℕ) : ℝ) := by
    intro s hs p q hp hpq hq
    obtain ⟨s₀, hs₀, hle, hge⟩ :=
      sub_side_of_recut ht hti (le_of_lt hik) hkt hs
    rw [← hccv s] at hle
    rw [← hccv (s + 1)] at hge
    exact hcqg s₀ hs₀ p q (le_trans hle hp) hpq (le_trans hq hge)
  -- the component is the side `t + 1` of the refined polygon
  have hgoal := hside (n + 2) (by omega) v w cc hlet hclosed hcc0 hccN hccmono hccqg
    lam (t + 1) (by omega)
    (by rw [hcc1, show t + 1 + 1 = t + 2 from by omega, hcc2]; exact hcomp)
    (by rw [hcc1]; exact hiso)
  rw [hcc1, show t + 1 + 1 = t + 2 from by omega, hcc2] at hgoal
  exact hgoal

end OsinComponents
end GGT
end GroupApproximation
