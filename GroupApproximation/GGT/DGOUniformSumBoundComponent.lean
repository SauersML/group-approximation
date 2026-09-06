import GroupApproximation.GGT.DGOProposition414AdditiveParameters
import GroupApproximation.GGT.DGOIsolatedComponentCollapseCut
import GroupApproximation.GGT.DGOIsolatedComponentSideForm

/-!
# The individual-component conclusion of a uniform DGO sum bound

A distinguished component can be collapsed to a single letter without losing
its span, isolation, or the other sides' quasi-geodesicity. The singleton
distinguished set then reads its bound directly from the uniform radius sum.
Recutting around an arbitrary component costs at most two extra sides.
-/

namespace GroupApproximation.GGT.OsinComponents

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.WordMetric

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- Uniform sum bounds persist when their radius coefficient is increased. -/
theorem DGOUniformSumBound.mono_radius
    {D : RelGenSet G Lambda} {mu c : ℝ} {C C' : ℕ}
    (hbound : DGOUniformSumBound D mu c C) (hCC' : C ≤ C') :
    DGOUniformSumBound D mu c C' := by
  intro n v word cut I lam hlet hclosed hcut hI hedge hcomp hiso hquasi
  obtain ⟨r, hr, hsum⟩ := hbound n v word cut I lam hlet hclosed hcut hI hedge hcomp hiso hquasi
  exact ⟨r, hr, hsum.trans (Nat.mul_le_mul_right n hCC')⟩

/-- A uniform sum bound controls a whole distinguished first-side component,
even when that component contains several letters. -/
theorem DGOUniformSumBound.sideZero_span
    {D : RelGenSet G Lambda} {mu b : ℝ} {C N : ℕ}
    (hbound : DGOUniformSumBound D mu b C)
    (v : G) (w : List (RelLetter G Lambda)) (c : ℕ → ℕ)
    (hlet : ∀ a ∈ w, D.IsLetter a) (hclosed : RelLetter.listVal w = 1)
    (hc0 : c 0 = 0) (hcN : c N = w.length) (hcmono : ∀ t, c t ≤ c (t + 1))
    (lam : Lambda)
    (hcqg : ∀ t, t < N → t ≠ 0 → ∀ p q, c t ≤ p → p ≤ q → q ≤ c (t + 1) →
      ((q - p : ℕ) : ℝ) / mu - b ≤
        ((wordDist D.alphabet.carrier (vertex v w p) (vertex v w q) : ℕ) : ℝ))
    (hcomp : IsComp lam w (c 0) (c 1)) (hiso : IsIsolated D.fam lam v w (c 0)) :
    (vertex v w (c 0))⁻¹ * vertex v w (c 1) ∈ D.relBall lam (C * N) := by
  classical
  rw [hc0] at hcomp hiso ⊢
  have hN : 1 ≤ N := by
    by_contra hn
    have hzero : N = 0 := by omega
    rw [hzero, hc0] at hcN
    have hlen := hcomp.2.1
    have hpos := hcomp.1
    omega
  let g := RelLetter.listVal (w.take (c 1))
  have hspan : vertex v w 0 * g = vertex v w (c 1) := by
    simp only [vertex_zero]
    exact (vertex_eq_mul_listVal_take w v (c 1)).symm
  have hg : g ∈ D.fam lam := by
    have h := span_mem_fam_of_isComp D v hlet hcomp
    rwa [← hspan, inv_mul_cancel_left] at h
  let q := normWord w lam 0 (c 1) g
  have hqlet : ∀ a ∈ q, D.IsLetter a := letters_normWord D hlet lam 0 (c 1) hg
  have hqclosed : RelLetter.listVal q = 1 := by
    have h := listVal_normWord w lam (i := 0) (k := c 1) (Nat.zero_le _)
    simpa only [List.drop_zero, Nat.sub_zero, hclosed] using h
  obtain ⟨d, hd0, hd1, hdN, hdmono, hdqg⟩ := exists_collapse_cut D mu b rfl hcN hcmono hN
    (Nat.succ_le_of_lt hcomp.1) hspan hcqg
  have hqcomp : IsComp lam q 0 1 := isComp_normWord w lam g hcomp
  have hqiso : IsIsolated D.fam lam v q 0 := isIsolated_normWord D v g hcomp hspan hiso
  obtain ⟨r, hr, hsum⟩ := hbound N v q d {0} (fun _ => lam) hqlet hqclosed
    ⟨hd0, hdN, hdmono⟩
    (by intro s hs; simp only [Finset.mem_singleton] at hs; subst s; omega)
    (by intro s hs; simp only [Finset.mem_singleton] at hs; subst s; simp [hd0, hd1])
    (by intro s hs; simp only [Finset.mem_singleton] at hs; subst s; simpa only [hd0, hd1] using hqcomp)
    (by intro s hs; simp only [Finset.mem_singleton] at hs; subst s; simpa only [hd0] using hqiso)
    (by intro s hs hnot; exact hdqg s hs (by simpa only [Finset.mem_singleton] using hnot))
  have hmem := hr 0 (Finset.mem_singleton_self 0)
  have hnormSpan : (vertex v q 0)⁻¹ * vertex v q 1 = g := by simp [q, normWord, RelLetter.val]
  rw [hd0, hd1, hnormSpan] at hmem
  have hbudget : r 0 ≤ C * N := by simpa only [Finset.sum_singleton] using hsum
  rw [← hspan, inv_mul_cancel_left]
  exact relBall_mono_radius D lam hbudget hmem

/-- The individual-component conclusion follows from the uniform sum bound
with a factor of three for the recut polygon's side count. -/
theorem DGOUniformSumBound.component_span
    {D : RelGenSet G Lambda} {mu b : ℝ} {C : ℕ}
    (hbound : DGOUniformSumBound D mu b C) (N : ℕ) (v : G)
    (w : List (RelLetter G Lambda)) (hpoly : IsQuasiGeodesicPolygon D mu b N v w)
    (lam : Lambda) (i k : ℕ) (hcomp : IsComp lam w i k) (hiso : IsIsolated D.fam lam v w i) :
    (vertex v w i)⁻¹ * vertex v w k ∈ D.relBall lam ((3 * C) * N) := by
  obtain ⟨hlet, hclosed, c, hc0, hcN, hcmono, hcqg⟩ := hpoly
  have hik := hcomp.1
  have hkw := hcomp.2.1
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | hpos
    · exact absurd hcN (by omega)
    · exact hpos
  have hmono : Monotone c := monotone_nat_of_le_succ hcmono
  obtain ⟨t, ht, hti, hit⟩ := exists_side_of_index c hc0 N i hN (by omega)
  obtain ⟨t', ht', htk, hkt'⟩ := exists_side_of_index c hc0 N k hN (by omega)
  have htt' : t ≤ t' := by
    by_contra hnot
    have h := hmono (show t' + 1 ≤ t by omega)
    omega
  have hkey := isolatedComponent_span_of_baseCase D mu b C ht hti hit ht' htk hkt' htt'
    (fun v' w' c' hlet' hclosed' hc0' hcN' hcmono' lam' hcqg' hcomp' hiso' =>
      hbound.sideZero_span v' w' c' hlet' hclosed' hc0' hcN' hcmono' lam' hcqg' hcomp' hiso')
    hlet hclosed hc0 hcN hcmono hcqg hcomp hiso
  apply relBall_mono_radius D lam ?_ hkey
  calc
    C * (N + 2 - (t' - t)) ≤ C * (3 * N) := Nat.mul_le_mul_left C (by omega)
    _ = (3 * C) * N := by ring

end GroupApproximation.GGT.OsinComponents

#audit_axioms GroupApproximation.GGT.OsinComponents.DGOUniformSumBound.mono_radius
#audit_axioms GroupApproximation.GGT.OsinComponents.DGOUniformSumBound.sideZero_span
#audit_axioms GroupApproximation.GGT.OsinComponents.DGOUniformSumBound.component_span
