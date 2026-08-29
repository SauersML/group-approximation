import GroupApproximation.GGT.DGOIsolatedComponentRecut

/-!
# A component that straddles a corner, and the side it becomes

`DGOIsolatedComponentRecut` makes an isolated component a side when it lies
inside one side, and its docstring records why the straddling case defeats that
recut: all of a run's vertices lie in one coset of `H lam`, so any two are one
letter apart, and the quasi-geodesic clause for the side `[i,k]` would demand
`(k-i)/μ - b ≤ 1`, which at `(1,0)` reads `2 ≤ 1` for a run straddling one
corner.

That obstruction is an artefact of the repository's polygon predicate, not of the
mathematics.  Dahmani--Guirardel--Osin's Definition 4.13 works with a *pair*
`(P, I)`: the sides in `I` are isolated components, and **only the sides off `I`
are quasi-geodesic** — the distinguished component-side is exempt from the clause.
`OsinComponents.IsQuasiGeodesicPolygon` demands the clause on every side, which
is strictly stronger than what §4.2 ever uses.

So this module states the bound in the exempt form and recuts against it, and
then the straddling case costs nothing: delete the corners strictly inside the
run, insert `i` and `k`, and the new side `[i,k]` is the component, which needs
no clause.  Every other new side is an interval inside a single old side, so its
clause is quoted verbatim.

## Two side indices, not one

The consumer supplies the side carrying `i` and the side carrying `k`:
`c t ≤ i ≤ c (t+1)` and `c t' ≤ k ≤ c (t'+1)` with `t ≤ t'`.  The refined cut
function is

    c' s = if s ≤ t then c s else if s ≤ t+1 then i else if s ≤ t+2 then k
             else c (s - 2 + (t' - t)) ,

with `N = n + 2 - (t' - t)` sides: the old sides up to `t` clipped at `i`, the
component, the tail of side `t'` from `k`, and the old sides after `t'`.  The
corners strictly inside the run — the ones the collapse could not place, and the
whole source of the `b + 1` in `DGOIsolatedComponentNormalise` — are exactly the
`t' - t` corners this deletes.  `t = t'` recovers
`DGOIsolatedComponentRecut.span_mem_relBall_of_sideForm`, with `N = n + 2`.

## What this unblocks

Once the run is a side, no corner lies strictly inside it, so collapsing it to
the single letter of its span shifts every later index by one and the same
amount, leaving every other side's gaps and vertices untouched: the normalisation
of `DGOIsolatedComponentNormalise` then costs nothing either.  Osin's Lemma 4.2
form for an arbitrary isolated component therefore follows from the side form at
`(1,0)`, with no constant loss and without quasi-geodesic stability — which is
the gap flagged for Lemma 4.9's discharge, where a run can end one side of a
geodesic triangle and continue into the next.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The refined cut function -/

/-- **Every side of the straddle-refined polygon except the component itself lies
inside a side of the old one.**

The side `s = t + 1` is the component and is excluded: it is the one side that is
not an interval inside an old side, and the one side Dahmani--Guirardel--Osin do
not ask a quasi-geodesic clause of.  As in `sub_side_of_recut`, the proof uses
only the inequalities positioning `i` and `k` in their sides — no monotonicity,
no metric input, and not even the lower bound `c t ≤ i` or the upper bound
`k ≤ c (t'+1)`, which are needed for monotonicity of the refined cut function but
not for this. -/
theorem sub_side_of_straddle_recut {c : ℕ → ℕ} {n t t' i k : ℕ} (ht : t < n)
    (hit : i ≤ c (t + 1)) (ht' : t' < n) (htk : c t' ≤ k) (htt' : t ≤ t')
    {s : ℕ} (hs : s < n + 2 - (t' - t)) (hst : s ≠ t + 1) :
    ∃ s₀ : ℕ, s₀ < n ∧
      c s₀ ≤ (if s ≤ t then c s else if s ≤ t + 1 then i
        else if s ≤ t + 2 then k else c (s - 2 + (t' - t))) ∧
      (if s + 1 ≤ t then c (s + 1) else if s + 1 ≤ t + 1 then i
        else if s + 1 ≤ t + 2 then k else c (s + 1 - 2 + (t' - t)))
        ≤ c (s₀ + 1) := by
  by_cases h1 : s + 1 ≤ t
  · exact ⟨s, by omega, le_of_eq (by rw [if_pos (show s ≤ t by omega)]),
      le_of_eq (by rw [if_pos h1])⟩
  · by_cases h2 : s ≤ t
    · -- `s = t`: the side `[c t, i]`
      refine ⟨t, ht, le_of_eq ?_, ?_⟩
      · rw [if_pos h2, show s = t from by omega]
      · rw [if_neg h1, if_pos (show s + 1 ≤ t + 1 by omega)]
        exact hit
    · -- `s = t + 1` is the component and is excluded
      by_cases h3 : s ≤ t + 1
      · exact absurd (show s = t + 1 from by omega) hst
      · by_cases h4 : s ≤ t + 2
        · -- `s = t + 2`: the tail `[k, c (t'+1)]` of the side carrying `k`
          refine ⟨t', ht', ?_, le_of_eq ?_⟩
          · rw [if_neg h2, if_neg h3, if_pos h4]
            exact htk
          · rw [if_neg (show ¬ s + 1 ≤ t by omega),
              if_neg (show ¬ s + 1 ≤ t + 1 by omega),
              if_neg (show ¬ s + 1 ≤ t + 2 by omega),
              show s + 1 - 2 + (t' - t) = t' + 1 from by omega]
        · -- an old side after `t'`
          refine ⟨s - 2 + (t' - t), by omega, le_of_eq ?_, le_of_eq ?_⟩
          · rw [if_neg h2, if_neg h3, if_neg h4]
          · rw [if_neg (show ¬ s + 1 ≤ t by omega),
              if_neg (show ¬ s + 1 ≤ t + 1 by omega),
              if_neg (show ¬ s + 1 ≤ t + 2 by omega),
              show s + 1 - 2 + (t' - t) = s - 2 + (t' - t) + 1 from by omega]

/-! ## The transfer, for an arbitrary isolated component -/

/-- **Osin's Lemma 4.2 form from Dahmani--Guirardel--Osin's side form, with no
hypothesis on where the component sits.**

The first binder is the side form of the §4.2 bound *in DGO's Definition 4.13
shape*: the quasi-geodesic clause is required only of the sides `s ≠ t`, `t` the
distinguished component's side.  Everything after it is proved.

The component may straddle any number of corners; the consumer supplies the side
`t` carrying its start and the side `t'` carrying its end.  The conclusion is at
`C * (n + 2)`, the refined polygon having `n + 2 - (t' - t) ≤ n + 2` sides.

With the clause demanded on *every* side this is false, and sharply so: at
`(1,0)` a run straddling one corner has one letter on each side of it, and the
side `[i,k]` would need `2 ≤ d ≤ 1`. That is the whole reason the exempt form is
the right hypothesis, and it is the form Dahmani--Guirardel--Osin state. -/
theorem span_mem_relBall_of_sideForm_straddle (D : RelGenSet G Λ) (mu b : ℝ)
    (C : ℕ)
    (hside : ∀ (N : ℕ), N ≤ 6 → ∀ (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ),
      (∀ a ∈ w, D.IsLetter a) → RelLetter.listVal w = 1 → c 0 = 0 →
      c N = w.length → (∀ s : ℕ, c s ≤ c (s + 1)) →
      ∀ (lam : Λ) (t : ℕ), t < N →
      (∀ s : ℕ, s < N → s ≠ t → ∀ p q : ℕ, c s ≤ p → p ≤ q →
        q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / mu - b
          ≤ ((wordDist D.alphabet.carrier (vertex v w p)
              (vertex v w q) : ℕ) : ℝ)) →
      IsComp lam w (c t) (c (t + 1)) → IsIsolated D.fam lam v w (c t) →
        (vertex v w (c t))⁻¹ * vertex v w (c (t + 1)) ∈ D.relBall lam (C * N))
    {n : ℕ} (hn : n ≤ 4) {v : G} {w : List (RelLetter G Λ)} {c : ℕ → ℕ}
    (hlet : ∀ a ∈ w, D.IsLetter a) (hclosed : RelLetter.listVal w = 1)
    (hc0 : c 0 = 0) (hcn : c n = w.length) (hcmono : ∀ s : ℕ, c s ≤ c (s + 1))
    (hcqg : ∀ s : ℕ, s < n → ∀ p q : ℕ, c s ≤ p → p ≤ q → q ≤ c (s + 1) →
      ((q - p : ℕ) : ℝ) / mu - b
        ≤ ((wordDist D.alphabet.carrier (vertex v w p) (vertex v w q) : ℕ) : ℝ))
    {lam : Λ} {i k t t' : ℕ} (ht : t < n) (hti : c t ≤ i) (hit : i ≤ c (t + 1))
    (ht' : t' < n) (htk : c t' ≤ k) (hkt' : k ≤ c (t' + 1)) (htt' : t ≤ t')
    (hcomp : IsComp lam w i k) (hiso : IsIsolated D.fam lam v w i) :
    (vertex v w i)⁻¹ * vertex v w k ∈ D.relBall lam (C * (n + 2)) := by
  have hik : i < k := hcomp.1
  set cc : ℕ → ℕ := fun s => if s ≤ t then c s else if s ≤ t + 1 then i
    else if s ≤ t + 2 then k else c (s - 2 + (t' - t))
  have hccv : ∀ s : ℕ, cc s = if s ≤ t then c s else if s ≤ t + 1 then i
      else if s ≤ t + 2 then k else c (s - 2 + (t' - t)) := fun s => rfl
  have hccle : ∀ s : ℕ, s ≤ t → cc s = c s := by
    intro s hs
    rw [hccv s, if_pos hs]
  have hcc1 : cc (t + 1) = i := by
    rw [hccv, if_neg (show ¬ t + 1 ≤ t by omega), if_pos (le_refl (t + 1))]
  have hcc2 : cc (t + 2) = k := by
    rw [hccv, if_neg (show ¬ t + 2 ≤ t by omega),
      if_neg (show ¬ t + 2 ≤ t + 1 by omega), if_pos (le_refl (t + 2))]
  have hccge : ∀ s : ℕ, t + 3 ≤ s → cc s = c (s - 2 + (t' - t)) := by
    intro s hs
    rw [hccv s, if_neg (show ¬ s ≤ t by omega), if_neg (show ¬ s ≤ t + 1 by omega),
      if_neg (show ¬ s ≤ t + 2 by omega)]
  -- the refined cut function is a cut function, with `n + 2 - (t' - t)` sides
  have hcc0 : cc 0 = 0 := by
    rw [hccle 0 (Nat.zero_le t), hc0]
  have hccN : cc (n + 2 - (t' - t)) = w.length := by
    rw [hccge (n + 2 - (t' - t)) (by omega),
      show n + 2 - (t' - t) - 2 + (t' - t) = n from by omega, hcn]
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
              show t + 3 - 2 + (t' - t) = t' + 1 from by omega]
            exact hkt'
          · rw [hccge s h4, hccge (s + 1) (by omega),
              show s + 1 - 2 + (t' - t) = s - 2 + (t' - t) + 1 from by omega]
            exact hcmono (s - 2 + (t' - t))
  -- every side but the component's is inside an old side
  have hccqg : ∀ s : ℕ, s < n + 2 - (t' - t) → s ≠ t + 1 → ∀ p q : ℕ, cc s ≤ p →
      p ≤ q → q ≤ cc (s + 1) → ((q - p : ℕ) : ℝ) / mu - b
        ≤ ((wordDist D.alphabet.carrier (vertex v w p) (vertex v w q) : ℕ) : ℝ) := by
    intro s hs hst p q hp hpq hq
    obtain ⟨s₀, hs₀, hle, hge⟩ :=
      sub_side_of_straddle_recut ht hit ht' htk htt' hs hst
    rw [← hccv s] at hle
    rw [← hccv (s + 1)] at hge
    exact hcqg s₀ hs₀ p q (le_trans hle hp) hpq (le_trans hq hge)
  -- the component is the side `t + 1` of the refined polygon
  have hgoal := hside (n + 2 - (t' - t)) (by omega) v w cc hlet hclosed hcc0 hccN
    hccmono lam (t + 1) (by omega) hccqg
    (by rw [hcc1, show t + 1 + 1 = t + 2 from by omega, hcc2]; exact hcomp)
    (by rw [hcc1]; exact hiso)
  rw [hcc1, show t + 1 + 1 = t + 2 from by omega, hcc2] at hgoal
  refine relBall_mono_radius D lam ?_ hgoal
  exact Nat.mul_le_mul le_rfl (by omega)

end OsinComponents
end GGT
end GroupApproximation
