import GroupApproximation.GGT.DGOPolygonCutFourGon
import GroupApproximation.GGT.DGOPolygonFarGon
import GroupApproximation.GGT.DGOPolygonEdgeGon
import GroupApproximation.GGT.DGOIsolatedComponentSplit
import GroupApproximation.GGT.OsinGeodesicWord

/-!
# Dahmani--Guirardel--Osin, Lemma 4.17: one step of the recursion

Cut the `n`-gon by a geodesic `q` from `x₃` back to `x₀`.  Either no component of
`q` is connected to the distinguished component `p₀` --- and then `p₀` is an
isolated component of the near 4-gon, `DGOPolygonCutFourGon` --- or one is, and
then the split

`(x₀⁻¹ · x₁) = (x₀⁻¹ · s₋) · (s₋⁻¹ · x₁)`

bounds `p₀` by the `(n-1)`-gon (`DGOPolygonFarGon`) plus a 4-gon
(`DGOPolygonEdgeGon`).  That is their `s(n) ≤ s(n-1) + s(4)` for one component;
with `s(m) = C · m` the constants add, `C₁ · 4 + C₂ · N ≤ (C₁ + C₂) · n`.

## Where the chord component sits

Our chord runs from `x₃` *to* `x₀`, so a component of it connected to `p₀` has
its initial vertex one letter from the chord's *far* endpoint.  The chord being
geodesic, the suffix from that component to the end has length at most one: the
component is the chord's last letter, and is a single letter.  This replaces
Dahmani--Guirardel--Osin's `s₊` argument, which reads the same fact off the
other orientation.

## Trivial sides

The cut is honest only when `c 1 < c 3`: the letter at `c 1` must stay a letter
of `w` in both cut polygons.  It fails only when sides `1` and `2` are both
trivial, and then `DGOPolygonJoin.baseCase_of_dropEmpty` sheds side `1` and the
`N`-gon bound applies with no cut at all.

Nothing here is metric: no hyperbolicity, no thinness, no Ol'shanskii cut.  The
only geometric input is that a geodesic word realises its length as a distance.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **Dahmani--Guirardel--Osin, Lemma 4.17, one step.**

From the 4-gon bound with constant `C₁` and the `N`-gon bound with constant
`C₂`, the `(N+1)`-gon bound with constant `C₁ + C₂`.

The three cases are: a trivial side, which sheds; no chord component connected
to the distinguished one, which is the near 4-gon; and one connected, which is
the split. -/
theorem span_mem_relBall_of_recursionStep (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (mu b : ℝ) (hmu : 1 ≤ mu)
    (hb : 0 ≤ b) (C₁ C₂ : ℕ) {n N : ℕ}
    (hnN : n = N + 1) (h4N : 4 ≤ N)
    (hbase : ∀ (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ),
      (∀ a ∈ w, D.IsLetter a) → RelLetter.listVal w = 1 → c 0 = 0 →
      c 4 = w.length → (∀ s : ℕ, c s ≤ c (s + 1)) → ∀ lam : Λ,
      (∀ s : ℕ, s < 4 → s ≠ 0 → ∀ p q : ℕ, c s ≤ p → p ≤ q →
        q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / mu - b
          ≤ ((wordDist D.alphabet.carrier (vertex v w p)
              (vertex v w q) : ℕ) : ℝ)) →
      IsComp lam w (c 0) (c 1) → IsIsolated D.fam lam v w (c 0) →
        (vertex v w (c 0))⁻¹ * vertex v w (c 1) ∈ D.relBall lam (C₁ * 4))
    (hprev : ∀ (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ),
      (∀ a ∈ w, D.IsLetter a) → RelLetter.listVal w = 1 → c 0 = 0 →
      c N = w.length → (∀ s : ℕ, c s ≤ c (s + 1)) → ∀ lam : Λ,
      (∀ s : ℕ, s < N → s ≠ 0 → ∀ p q : ℕ, c s ≤ p → p ≤ q →
        q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / mu - b
          ≤ ((wordDist D.alphabet.carrier (vertex v w p)
              (vertex v w q) : ℕ) : ℝ)) →
      IsComp lam w (c 0) (c 1) → IsIsolated D.fam lam v w (c 0) →
        (vertex v w (c 0))⁻¹ * vertex v w (c 1) ∈ D.relBall lam (C₂ * N)) :
    ∀ (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ),
      (∀ a ∈ w, D.IsLetter a) → RelLetter.listVal w = 1 → c 0 = 0 →
      c n = w.length → (∀ s : ℕ, c s ≤ c (s + 1)) → ∀ lam : Λ,
      (∀ s : ℕ, s < n → s ≠ 0 → ∀ p q : ℕ, c s ≤ p → p ≤ q →
        q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / mu - b
          ≤ ((wordDist D.alphabet.carrier (vertex v w p)
              (vertex v w q) : ℕ) : ℝ)) →
      IsComp lam w (c 0) (c 1) → IsIsolated D.fam lam v w (c 0) →
        (vertex v w (c 0))⁻¹ * vertex v w (c 1)
          ∈ D.relBall lam ((C₁ + C₂) * n) := by
  intro v w c hlet hclosed hc0 hcn hcmono lam hcqg hcomp hiso
  have hmono : Monotone c := monotone_nat_of_le_succ hcmono
  have h12 : c 1 ≤ c 2 := hmono (by omega)
  have h23 : c 2 ≤ c 3 := hmono (by omega)
  have hc3w : c 3 ≤ w.length := by
    have h := hmono (show 3 ≤ n by omega)
    rw [hcn] at h
    exact h
  rcases Nat.lt_or_ge (c 1) (c 3) with hc13 | hge
  · -- the cut is honest
    obtain ⟨q, hq⟩ := existsGeodesicWord D (vertex v w (c 3)) v
    by_cases hchord : ∀ t : ℕ, IsCompStart lam q t →
        ¬ Connected D.fam lam v (joinWord w (c 3) q) (c 0) (c 3 + t)
    · -- Case A: the distinguished component survives the cut isolated
      have hA := span_mem_relBall_of_noChordConnection D mu b hmu hb C₁ hbase v
        lam hlet hc0
        hcn hcmono (by omega) hcqg hcomp hiso hq hc13 hchord
      refine relBall_mono_radius D lam ?_ hA
      exact Nat.mul_le_mul (by omega) (by omega)
    · -- Case B: a component of the chord is connected to it
      have hex : ∃ t : ℕ, IsCompStart lam q t ∧
          Connected D.fam lam v (joinWord w (c 3) q) (c 0) (c 3 + t) := by
        by_contra hcon
        exact hchord (fun t hst hconn => hcon ⟨t, hst, hconn⟩)
      obtain ⟨t, hstart, hconnt⟩ := hex
      obtain ⟨k, hcompt⟩ := hstart
      have hmem : v⁻¹ * vertex (vertex v w (c 3)) q t ∈ D.fam lam := by
        have h : (vertex v (joinWord w (c 3) q) (c 0))⁻¹ *
            vertex v (joinWord w (c 3) q) (c 3 + t) ∈ D.fam lam := hconnt
        rwa [hc0, vertex_zero,
          vertex_joinWord_add v w q hc3w (c 3 + t) t rfl] at h
      -- the chord is geodesic, so its suffix from `t` has length at most one
      have hone := wordDist_le_one_of_mem_fam D hmem
      have hgeo := sub_le_wordDist_vertex D hq t q.length
        (by have h := hcompt.1; have h' := hcompt.2.1; omega) le_rfl
      rw [hq.vertex_length_eq, wordDist_comm D.alphabet.symmetricGenerating
        (vertex (vertex v w (c 3)) q t) v] at hgeo
      have ht : t = q.length - 1 := by
        have h := hcompt.1
        have h' := hcompt.2.1
        omega
      have hk : k = q.length := by
        have h := hcompt.1
        have h' := hcompt.2.1
        omega
      rw [ht, hk] at hcompt
      rw [ht] at hmem
      -- the two halves of the split
      have hfar := span_mem_relBall_of_farGon D hsymm mu b hmu hb C₂ hprev v
        lam hlet
        hclosed hc0 hcn hcmono hnN (by omega) hcqg hcomp hiso hq hc13 hcompt hmem
      have hedge := span_mem_relBall_of_edgeGon D mu b hmu hb C₁ hbase v lam
        hlet hc0 hcn
        hcmono (by omega) hcqg hcomp hiso hq hc13 hcompt hmem
      have hsplit := span_mem_relBall_of_split D lam hfar hedge
      rw [show (vertex v w (c 0))⁻¹ * vertex v w (c 1)
        = v⁻¹ * vertex v w (c 1) from by rw [hc0, vertex_zero]]
      refine relBall_mono_radius D lam ?_ hsplit
      have e1 : C₂ * N ≤ C₂ * n := Nat.mul_le_mul le_rfl (by omega)
      have e2 : C₁ * 4 ≤ C₁ * n := Nat.mul_le_mul le_rfl (by omega)
      calc C₂ * N + C₁ * 4 ≤ C₂ * n + C₁ * n := Nat.add_le_add e1 e2
        _ = (C₁ + C₂) * n := by ring
  · -- sides `1` and `2` are both trivial; shed side `1`
    have hT := baseCase_of_dropEmpty D mu b C₂ hprev v w c hlet hclosed hc0
      (by rw [← hnN]; exact hcn) hcmono lam
      (fun s hs hs0 p q' hp hpq hq' => hcqg s (by omega) hs0 p q' hp hpq hq')
      hcomp hiso (j := 1) (by omega) (by omega)
      (by rw [show (1 : ℕ) + 1 = 2 from by norm_num]; omega)
    refine relBall_mono_radius D lam ?_ hT
    exact Nat.mul_le_mul (by omega) (by omega)

/-- **The 5-gon case**, from the 4-gon case alone: the far polygon of a 5-gon is
a 4-gon, so one step suffices. -/
theorem span_mem_relBall_of_fiveGon (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (mu b : ℝ) (hmu : 1 ≤ mu)
    (hb : 0 ≤ b) (C : ℕ)
    (hbase : ∀ (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ),
      (∀ a ∈ w, D.IsLetter a) → RelLetter.listVal w = 1 → c 0 = 0 →
      c 4 = w.length → (∀ s : ℕ, c s ≤ c (s + 1)) → ∀ lam : Λ,
      (∀ s : ℕ, s < 4 → s ≠ 0 → ∀ p q : ℕ, c s ≤ p → p ≤ q →
        q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / mu - b
          ≤ ((wordDist D.alphabet.carrier (vertex v w p)
              (vertex v w q) : ℕ) : ℝ)) →
      IsComp lam w (c 0) (c 1) → IsIsolated D.fam lam v w (c 0) →
        (vertex v w (c 0))⁻¹ * vertex v w (c 1) ∈ D.relBall lam (C * 4)) :
    ∀ (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ),
      (∀ a ∈ w, D.IsLetter a) → RelLetter.listVal w = 1 → c 0 = 0 →
      c 5 = w.length → (∀ s : ℕ, c s ≤ c (s + 1)) → ∀ lam : Λ,
      (∀ s : ℕ, s < 5 → s ≠ 0 → ∀ p q : ℕ, c s ≤ p → p ≤ q →
        q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / mu - b
          ≤ ((wordDist D.alphabet.carrier (vertex v w p)
              (vertex v w q) : ℕ) : ℝ)) →
      IsComp lam w (c 0) (c 1) → IsIsolated D.fam lam v w (c 0) →
        (vertex v w (c 0))⁻¹ * vertex v w (c 1) ∈ D.relBall lam ((C + C) * 5) :=
  span_mem_relBall_of_recursionStep D hsymm mu b hmu hb C C (N := 4)
    (by norm_num) (by norm_num) hbase hbase

/-- **The 6-gon case**, from the 4-gon case: its far polygon is the 5-gon just
proved. -/
theorem span_mem_relBall_of_sixGon (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (mu b : ℝ) (hmu : 1 ≤ mu)
    (hb : 0 ≤ b) (C : ℕ)
    (hbase : ∀ (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ),
      (∀ a ∈ w, D.IsLetter a) → RelLetter.listVal w = 1 → c 0 = 0 →
      c 4 = w.length → (∀ s : ℕ, c s ≤ c (s + 1)) → ∀ lam : Λ,
      (∀ s : ℕ, s < 4 → s ≠ 0 → ∀ p q : ℕ, c s ≤ p → p ≤ q →
        q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / mu - b
          ≤ ((wordDist D.alphabet.carrier (vertex v w p)
              (vertex v w q) : ℕ) : ℝ)) →
      IsComp lam w (c 0) (c 1) → IsIsolated D.fam lam v w (c 0) →
        (vertex v w (c 0))⁻¹ * vertex v w (c 1) ∈ D.relBall lam (C * 4)) :
    ∀ (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ),
      (∀ a ∈ w, D.IsLetter a) → RelLetter.listVal w = 1 → c 0 = 0 →
      c 6 = w.length → (∀ s : ℕ, c s ≤ c (s + 1)) → ∀ lam : Λ,
      (∀ s : ℕ, s < 6 → s ≠ 0 → ∀ p q : ℕ, c s ≤ p → p ≤ q →
        q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / mu - b
          ≤ ((wordDist D.alphabet.carrier (vertex v w p)
              (vertex v w q) : ℕ) : ℝ)) →
      IsComp lam w (c 0) (c 1) → IsIsolated D.fam lam v w (c 0) →
        (vertex v w (c 0))⁻¹ * vertex v w (c 1)
          ∈ D.relBall lam ((C + (C + C)) * 6) :=
  span_mem_relBall_of_recursionStep D hsymm mu b hmu hb C (C + C) (N := 5)
    (by norm_num) (by norm_num) hbase
    (span_mem_relBall_of_fiveGon D hsymm mu b hmu hb C hbase)

end OsinComponents
end GGT
end GroupApproximation
