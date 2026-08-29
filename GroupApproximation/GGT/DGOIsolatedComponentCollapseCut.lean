import GroupApproximation.GGT.DGOIsolatedComponentNormalise

/-!
# Collapsing the first side to one letter, at the level of the polygon

`DGOIsolatedComponentNormalise` collapses a run to the single letter of its span
and carries the component and its isolation across.  This module carries the
*polygon* across: the cut function, the endpoints, monotonicity, and the
quasi-geodesic clause.

It is stated only for the collapse at index `0`, which is the only one the
pipeline performs.  That is not a restriction but a simplification: the recut
makes the component a side and the rotation puts that side first, so the prefix
`w.take 0` is empty, `normWord w lam 0 K s = comp lam s :: w.drop K`, and the
index map is as simple as it can be — `0 ↦ 0`, and `p ↦ K + p - 1` for `p ≥ 1`.

Concept grep before writing: `cut function`, `Monotone c`, `c 1 = 1` across the
DGO files.  `DGOIsolatedComponentRecut` and `…Straddle` refine a cut function;
`DGOPolygonGeodesicChain` carries one in `GeodesicFourGon`; none of them
transports one along a change of word.

## Why the clause transfers verbatim

Every side but the first keeps both of its endpoints and its index gap: side `t`
runs from `c t` to `c (t+1)` in `w` and from `c t - (K-1)` to `c (t+1) - (K-1)`
in the collapsed word, whose vertices at those indices are the same group
elements (`vertex_normWord_add`).  So the clause is quoted, not reproved — no
metric input, and no constant is lost.  The first side is the component, and
under Dahmani--Guirardel--Osin's Definition 4.13 it carries no clause; what it
carries instead is `d 1 = 1`, which is what the base case reads as "the
distinguished side is a single letter".
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The collapsed cut function -/

/-- **The polygon survives the collapse of its first side.**

Given a polygon whose first side `[0, K)` is the distinguished component — so
exempt from the quasi-geodesic clause, which is asked only of the sides `t ≠ 0` —
the collapsed word carries a cut function with the same number of sides, the same
clause on every side but the first, and `d 1 = 1`: the first side is now a single
letter, with the same span.

`hspan` says `s` is the span of the collapsed run; it is what
`span_mem_fam_of_isComp` supplies, and it is the only hypothesis relating `s` to
`w`. -/
theorem exists_collapse_cut (D : RelGenSet G Λ) (mu b : ℝ) {N K : ℕ} {v : G}
    {w : List (RelLetter G Λ)} {c : ℕ → ℕ} {lam : Λ} {s : G}
    (hc1 : c 1 = K) (hcN : c N = w.length)
    (hcmono : ∀ t : ℕ, c t ≤ c (t + 1)) (hN : 1 ≤ N) (hK : 1 ≤ K)
    (hspan : vertex v w 0 * s = vertex v w K)
    (hcqg : ∀ t : ℕ, t < N → t ≠ 0 → ∀ p q : ℕ, c t ≤ p → p ≤ q →
      q ≤ c (t + 1) → ((q - p : ℕ) : ℝ) / mu - b
        ≤ ((wordDist D.alphabet.carrier (vertex v w p) (vertex v w q) : ℕ) : ℝ)) :
    ∃ d : ℕ → ℕ, d 0 = 0 ∧ d 1 = 1 ∧
      d N = (normWord w lam 0 K s).length ∧ (∀ t : ℕ, d t ≤ d (t + 1)) ∧
      ∀ t : ℕ, t < N → t ≠ 0 → ∀ p q : ℕ, d t ≤ p → p ≤ q →
        q ≤ d (t + 1) → ((q - p : ℕ) : ℝ) / mu - b
          ≤ ((wordDist D.alphabet.carrier
              (vertex v (normWord w lam 0 K s) p)
              (vertex v (normWord w lam 0 K s) q) : ℕ) : ℝ) := by
  have hmono : Monotone c := monotone_nat_of_le_succ hcmono
  have hKw : K ≤ w.length := by
    have h := hmono hN
    rw [hc1, hcN] at h
    exact h
  have hlen : (normWord w lam 0 K s).length = w.length - K + 1 := by
    rw [length_normWord w lam 0 K s (Nat.zero_le _)]
    omega
  -- every corner but the first sits at or after `K`
  have hcK : ∀ t : ℕ, 1 ≤ t → K ≤ c t := by
    intro t ht
    have h := hmono ht
    rw [hc1] at h
    exact h
  -- the vertices of the collapsed word, at the shifted corners
  have hvert : ∀ p : ℕ, 1 ≤ p →
      vertex v (normWord w lam 0 K s) p = vertex v w (K + (p - 1)) :=
    fun p hp => vertex_normWord_add v w lam 0 K s (Nat.zero_le _) hspan p (p - 1)
      (by omega)
  refine ⟨fun t => if t = 0 then 0 else c t - (K - 1), by simp, ?_, ?_, ?_, ?_⟩
  · show (if (1 : ℕ) = 0 then 0 else c 1 - (K - 1)) = 1
    rw [if_neg (by omega), hc1]
    omega
  · show (if N = 0 then 0 else c N - (K - 1)) = (normWord w lam 0 K s).length
    rw [if_neg (by omega), hcN, hlen]
    omega
  · intro t
    show (if t = 0 then 0 else c t - (K - 1))
        ≤ (if t + 1 = 0 then 0 else c (t + 1) - (K - 1))
    rw [if_neg (show ¬ t + 1 = 0 by omega)]
    by_cases ht : t = 0
    · rw [if_pos ht]
      exact Nat.zero_le _
    · rw [if_neg ht]
      have := hcmono t
      omega
  · intro t htN ht0 p q hp hpq hq
    have hp' : c t - (K - 1) ≤ p := by
      have : (if t = 0 then 0 else c t - (K - 1)) ≤ p := hp
      rwa [if_neg ht0] at this
    have hq' : q ≤ c (t + 1) - (K - 1) := by
      have : q ≤ (if t + 1 = 0 then 0 else c (t + 1) - (K - 1)) := hq
      rwa [if_neg (show ¬ t + 1 = 0 by omega)] at this
    have hKt : K ≤ c t := hcK t (by omega)
    have hKt1 : K ≤ c (t + 1) := hcK (t + 1) (by omega)
    have hp1 : 1 ≤ p := by omega
    have hq1 : 1 ≤ q := by omega
    have hkey := hcqg t htN ht0 (K + (p - 1)) (K + (q - 1)) (by omega) (by omega)
      (by omega)
    rw [show K + (q - 1) - (K + (p - 1)) = q - p from by omega] at hkey
    rw [hvert p hp1, hvert q hq1]
    exact hkey

end OsinComponents
end GGT
end GroupApproximation
