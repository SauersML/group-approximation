import GroupApproximation.GGT.DGOQuasiGeodesicFourGonBounds
import GroupApproximation.GGT.DGOIsolatedComponentCollapseCut

/-!
# Collapsing the exempt component at general quasi-geodesic parameters

The exempt component fills the first side, so no non-exempt side has a corner
inside it. The collapse therefore preserves both quasi-geodesic parameters,
the component's span, and isolation. The new first side has exactly one letter.
-/

namespace GroupApproximation.GGT.OsinComponents

open GroupApproximation.WordMetric

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- Normalisation of the exempt side, with the multiplicative constant retained. -/
theorem QuasiGeodesicFourGon.exists_unit_side_zero
    (D : RelGenSet G Lambda) {mu : ℝ} {b : ℕ} {v : G}
    {w : List (RelLetter G Lambda)} {c : ℕ → ℕ}
    (hQ : QuasiGeodesicFourGon D mu b v w c)
    {lam : Lambda} (hcomp : IsComp lam w (c 0) (c 1))
    (hiso : IsIsolated D.fam lam v w (c 0)) :
    ∃ (q : List (RelLetter G Lambda)) (d : ℕ → ℕ),
      QuasiGeodesicFourGon D mu b v q d ∧ d 1 = 1 ∧
        IsComp lam q 0 1 ∧ IsIsolated D.fam lam v q 0 ∧
        (vertex v q 0)⁻¹ * vertex v q 1 =
          (vertex v w (c 0))⁻¹ * vertex v w (c 1) := by
  have hc0 := hQ.start
  rw [hc0] at hcomp hiso ⊢
  let g := RelLetter.listVal (w.take (c 1))
  have hspan : vertex v w 0 * g = vertex v w (c 1) := by
    simp only [vertex_zero]
    exact (vertex_eq_mul_listVal_take w v (c 1)).symm
  have hg : g ∈ D.fam lam := by
    have h := span_mem_fam_of_isComp D v hQ.letters hcomp
    rwa [← hspan, inv_mul_cancel_left] at h
  let q := normWord w lam 0 (c 1) g
  have hlet : ∀ a ∈ q, D.IsLetter a := letters_normWord D hQ.letters lam 0 (c 1) hg
  have hclosed : RelLetter.listVal q = 1 := by
    have h := listVal_normWord w lam (i := 0) (k := c 1) (Nat.zero_le _)
    simpa only [List.drop_zero, Nat.sub_zero, hQ.closed] using h
  obtain ⟨d, hd0, hd1, hd4, hdmono, hdqg⟩ :=
    exists_collapse_cut D mu (b : ℝ) rfl hQ.finish
      (fun t => hQ.mono (Nat.le_succ t)) (by norm_num : 1 ≤ 4)
      (Nat.succ_le_of_lt hcomp.1) hspan
      (fun s hs hs0 p q hp hpq hq => (hQ.side_dist_of_mem D hs hs0 hp hpq hq).1)
  have hdMono : Monotone d := monotone_nat_of_le_succ hdmono
  refine ⟨q, d, ⟨hlet, hclosed, hd0, hd4, hdMono, ?_⟩, hd1,
    isComp_normWord w lam g hcomp, isIsolated_normWord D v g hcomp hspan hiso, ?_⟩
  · intro s hs hs0 p r hpr hr
    have hd : d s ≤ d (s + 1) := hdmono s
    have hside : d (s + 1) ≤ q.length := by
      have h := hdMono (show s + 1 ≤ 4 by omega)
      simpa only [hd4] using h
    have hlower := hdqg s hs hs0 (d s + p) (d s + r) (by omega) (by omega) (by omega)
    have hupper := wordDist_vertex_le' D hlet v
      (show d s + p ≤ d s + r by omega) (show d s + r ≤ q.length by omega)
    have hdiff : d s + r - (d s + p) = r - p := by omega
    exact ⟨by simpa only [hdiff] using hlower, by simpa only [hdiff] using hupper⟩
  · have hnormSpan : (vertex v q 0)⁻¹ * vertex v q 1 = g := by
      simp [q, normWord, RelLetter.val]
    rw [hnormSpan, ← hspan, inv_mul_cancel_left]

end GroupApproximation.GGT.OsinComponents

#audit_axioms GroupApproximation.GGT.OsinComponents.QuasiGeodesicFourGon.exists_unit_side_zero
