import GroupApproximation.GGT.SystolicCurvature
import GroupApproximation.GGT.SystolicGraphConditions
import GroupApproximation.Meta.AxiomGuard

/-!
# Short cycles in the one-skeleton of a 6-large triangle complex

A closed edge path bounds a least disc whose interior vertices have degree at least six
(go-sr1's `exists_leastDisc_typedLinks` at the constant bound six).  If the path runs through
distinct vertices and no boundary vertex has degree two, every boundary vertex carries curvature
at most one, so the count `boundary_curvature_ge_six` forces at least six boundary vertices.

* `exists_disc_of_cycle`: a closed edge path `g 0, …, g n = g 0` bounds such a disc, read
  along `g`.
* `TriangulatedDisc.SimpleBoundary.three_le_bdeg`: a boundary vertex whose two boundary
  neighbours are not adjacent has degree at least three.
* `TriangulatedDisc.SimpleBoundary.six_le_blen`: a simple boundary all of whose vertices have
  degree at least three has length at least six.
* `noInducedFourCycle_of_linksSixLarge`, `noInducedFiveCycle_of_linksSixLarge`: every cycle of
  length four or five through distinct vertices has a chord.

## Manuscript status

Infrastructure for the torsion-free hyperbolic property (T) witness on the
Kotowski--Ollivier route; certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace Systolic

open GGT.VanKampen

universe u

variable {V : Type u} {X : TriangleComplex V}

/-- 6-large links give the constant link bound six. -/
theorem linksLargeAt_six (h6 : LinksSixLarge X) : LinksLargeAt X (fun _ => 6) := by
  intro v c h3 hlt hnd hadj
  have hlt' : c.length < 6 := hlt
  exact h6 v c h3 (by omega) hnd hadj

namespace TriangulatedDisc

variable {γ : List V} (D : TriangulatedDisc X γ)

theorem bvert_add_blen (k : ℕ) : D.bvert (k + D.blen) = D.bvert k := by
  unfold bvert
  rw [D.bdart_add_blen]

theorem bdeg_add_blen (k : ℕ) : D.bdeg (k + D.blen) = D.bdeg k := by
  unfold bdeg
  rw [D.bvert_add_blen]

variable {D}

/-- A disc read along a path through distinct vertices has a simple boundary. -/
theorem simpleBoundary_of_ne {n : ℕ} (h3 : 3 ≤ n) (hblen : D.blen = n) {g : ℕ → V}
    (hg : ∀ i, i ≤ n → D.vtx (D.bvert i) = g i) (hne : ∀ i j, i < j → j < n → g i ≠ g j) :
    D.SimpleBoundary := by
  refine ⟨by omega, fun i j hi hj h => ?_⟩
  rw [hg i (by omega), hg j (by omega)] at h
  by_contra hij
  obtain hlt | hlt : i < j ∨ j < i := by omega
  · exact hne i j hlt (by omega) h
  · exact hne j i hlt (by omega) h.symm

/-- A boundary vertex whose boundary neighbours are not adjacent has degree at least three. -/
theorem SimpleBoundary.three_le_bdeg (hS : D.SimpleBoundary)
    (h0 : ¬ X.G.Adj (D.vtx (D.bvert (D.blen - 1))) (D.vtx (D.bvert 1)))
    (h : ∀ k, k + 2 ≤ D.blen → ¬ X.G.Adj (D.vtx (D.bvert k)) (D.vtx (D.bvert (k + 2)))) :
    ∀ k, k < D.blen → 3 ≤ D.bdeg k := by
  have hpos := hS.blen_pos
  intro k hk
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · have hwrap : D.blen - 1 + 1 = 0 + D.blen := by omega
    have h2 := hS.two_le_bdeg (D.blen - 1)
    rw [hwrap, D.bdeg_add_blen] at h2
    by_contra hlt
    have hadj := hS.adj_of_bdeg_two (D.blen - 1) (by rw [hwrap, D.bdeg_add_blen]; omega)
    have hwrap2 : D.blen - 1 + 2 = 1 + D.blen := by omega
    rw [hwrap2, D.bvert_add_blen] at hadj
    exact h0 hadj
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h2 := hS.two_le_bdeg j
    by_contra hlt
    exact h j (by omega) (hS.adj_of_bdeg_two j (by omega))

/-- **A simple boundary all of whose vertices have degree at least three has length at least
six**, when every interior vertex has degree at least six. -/
theorem SimpleBoundary.six_le_blen (hS : D.SimpleBoundary)
    (hint : ∀ w : D.map.Vertex, D.Interior w → 6 ≤ D.map.vertexDegree w)
    (h3 : ∀ k, k < D.blen → 3 ≤ D.bdeg k) : 6 ≤ D.blen := by
  have hsum := hS.boundary_curvature_ge_six hint
  have hle : ∑ k ∈ Finset.range D.blen, ((4 : ℤ) - D.bdeg k) ≤
      ∑ _k ∈ Finset.range D.blen, (1 : ℤ) :=
    Finset.sum_le_sum fun k hk => by
      have := h3 k (Finset.mem_range.mp hk)
      omega
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hle
  omega

end TriangulatedDisc

open TriangulatedDisc

/-- **A closed edge path bounds a least disc read along it.**  If `g 0, g 1, …, g n = g 0` is a
closed edge path with `n ≥ 2`, it bounds a triangulated disc of boundary length `n` whose
boundary vertex `i` maps to `g i` and whose interior vertices have degree at least six. -/
theorem exists_disc_of_cycle (hfill : FillingStatement X) (hfold : MirrorFoldStatement X)
    (h6 : LinksSixLarge X) {n : ℕ} (hn : 2 ≤ n) (g : ℕ → V) (hg : g n = g 0)
    (hadj : ∀ i, i < n → X.G.Adj (g i) (g (i + 1))) :
    ∃ (γ : List V) (D : TriangulatedDisc X γ),
      (∀ w : D.map.Vertex, D.Interior w → 6 ≤ D.map.vertexDegree w) ∧ D.blen = n ∧
        ∀ i, i ≤ n → D.vtx (D.bvert i) = g i := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hγ : (List.range (m + 1 + 1)).map g =
      g 0 :: (List.range m).map (g ∘ Nat.succ) ++ [g 0] := by
    rw [List.range_succ, List.map_append, List.range_succ_eq_map, List.map_cons, List.map_map,
      List.map_cons, List.map_nil, hg]
  have hchain : List.IsChain X.G.Adj (g 0 :: (List.range m).map (g ∘ Nat.succ) ++ [g 0]) := by
    rw [← hγ, List.isChain_map]
    exact (List.isChain_range_succ (fun a b => X.G.Adj (g a) (g b)) (m + 1)).mpr hadj
  have hne : (List.range m).map (g ∘ Nat.succ) ≠ [] := by
    intro h
    have hl := congrArg List.length h
    simp at hl
    omega
  obtain ⟨D, -, hint⟩ :=
    exists_leastDisc_typedLinks hfill hfold (linksLargeAt_six h6) hchain hne
  have hblen : D.blen = m + 1 := by
    have hlen := D.length_eq
    have h2 : (g 0 :: (List.range m).map (g ∘ Nat.succ) ++ [g 0]).length = m + 1 + 1 := by
      simp
    omega
  refine ⟨_, D, hint, hblen, fun i hi => ?_⟩
  have h1 := D.getElem?_eq (k := i) (by omega)
  have hi' : i < m + 1 + 1 := by omega
  have h2 : ((List.range (m + 1 + 1)).map g)[i]? = some (g i) := by
    rw [List.getElem?_map, List.getElem?_range hi', Option.map_some]
  rw [hγ] at h2
  exact Option.some.inj (h1.symm.trans h2)

/-- **No induced four-cycle** in the one-skeleton of a 6-large triangle complex. -/
theorem noInducedFourCycle_of_linksSixLarge (hfill : FillingStatement X)
    (hfold : MirrorFoldStatement X) (h6 : LinksSixLarge X) : NoInducedFourCycle X.G := by
  intro a b c d hab hbc hcd hda hac hbd
  by_contra hno
  push Not at hno
  obtain ⟨hnac, hnbd⟩ := hno
  obtain ⟨γ, D, hint, hblen, hg⟩ := exists_disc_of_cycle hfill hfold h6 (n := 4) (by norm_num)
    (fun i => match i with
      | 0 => a
      | 1 => b
      | 2 => c
      | 3 => d
      | _ => a) rfl fun i hi => by
      interval_cases i
      · exact hab
      · exact hbc
      · exact hcd
      · exact hda
  have hS : D.SimpleBoundary := simpleBoundary_of_ne (by norm_num) hblen hg fun i j hij hj => by
    interval_cases j <;> interval_cases i
    · exact hab.ne
    · exact hac
    · exact hbc.ne
    · exact hda.ne.symm
    · exact hbd
    · exact hcd.ne
  have hb0 : D.vtx (D.bvert (D.blen - 1)) = d := by
    rw [hblen]
    exact hg 3 (by norm_num)
  have hb1 : D.vtx (D.bvert 1) = b := hg 1 (by norm_num)
  have h3 := hS.three_le_bdeg (by rw [hb0, hb1]; exact fun h => hnbd h.symm) fun k hk => by
    have hk' : k < 3 := by omega
    rw [hg k (by omega), hg (k + 2) (by omega)]
    interval_cases k
    · exact hnac
    · exact hnbd
    · exact fun h => hnac h.symm
  have := hS.six_le_blen hint h3
  omega

/-- **No induced five-cycle** in the one-skeleton of a 6-large triangle complex. -/
theorem noInducedFiveCycle_of_linksSixLarge (hfill : FillingStatement X)
    (hfold : MirrorFoldStatement X) (h6 : LinksSixLarge X) : NoInducedFiveCycle X.G := by
  intro a b c d e hab hbc hcd hde hea hac had hbd hbe hce
  by_contra hno
  push Not at hno
  obtain ⟨hnac, hnad, hnbd, hnbe, hnce⟩ := hno
  obtain ⟨γ, D, hint, hblen, hg⟩ := exists_disc_of_cycle hfill hfold h6 (n := 5) (by norm_num)
    (fun i => match i with
      | 0 => a
      | 1 => b
      | 2 => c
      | 3 => d
      | 4 => e
      | _ => a) rfl fun i hi => by
      interval_cases i
      · exact hab
      · exact hbc
      · exact hcd
      · exact hde
      · exact hea
  have hS : D.SimpleBoundary := simpleBoundary_of_ne (by norm_num) hblen hg fun i j hij hj => by
    interval_cases j <;> interval_cases i
    · exact hab.ne
    · exact hac
    · exact hbc.ne
    · exact had
    · exact hbd
    · exact hcd.ne
    · exact hea.ne.symm
    · exact hbe
    · exact hce
    · exact hde.ne
  have hb0 : D.vtx (D.bvert (D.blen - 1)) = e := by
    rw [hblen]
    exact hg 4 (by norm_num)
  have hb1 : D.vtx (D.bvert 1) = b := hg 1 (by norm_num)
  have h3 := hS.three_le_bdeg (by rw [hb0, hb1]; exact fun h => hnbe h.symm) fun k hk => by
    have hk' : k < 4 := by omega
    rw [hg k (by omega), hg (k + 2) (by omega)]
    interval_cases k
    · exact hnac
    · exact hnbd
    · exact hnce
    · exact fun h => hnad h.symm
  have := hS.six_le_blen hint h3
  omega

end Systolic
end GroupApproximation

open GroupApproximation.Systolic

#audit_axioms linksLargeAt_six
#audit_axioms TriangulatedDisc.simpleBoundary_of_ne
#audit_axioms TriangulatedDisc.SimpleBoundary.three_le_bdeg
#audit_axioms TriangulatedDisc.SimpleBoundary.six_le_blen
#audit_axioms exists_disc_of_cycle
#audit_axioms noInducedFourCycle_of_linksSixLarge
#audit_axioms noInducedFiveCycle_of_linksSixLarge
