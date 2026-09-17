import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.SwitchCornerBridge
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundCaseOneFace
import GroupApproximation.GGT.HullSCLemma44RelativeDehn
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P01, empty two-gons: the triangle corner

Notation: `M = S.diagram.toCombMap`, `φ = M.facePerm`, `α = M.alpha`, `F = P.face k`.

This module proves `SwitchCornerOneStatement` (`switchCornerOne`), with thresholds `ε₀ = 2` and
`ρ₀ = 1`.  So `OneCornerExcluded P` holds for every maximal polygon system of a globally
distinguished section family with `ε ≥ 2`.  The second polygon `k′` is not used.

## Proof route

Let `d` be a dart of `F` with `α d` on `A = objectFace o` and `α (φ d)` on `B = objectFace o′`,
`o ≠ o′`.
1. *`φ d ≠ d`*, since otherwise `A = B` and `o = o′` (`objectFace_injective`).  So some rotation
   of the walk of `F` reads `d, φ d, L` (`exists_rotate_corner`).
2. *The value of `L`.*  `F` is no relator cell, so its word has value `1` (`face_value`), and so
   has its rotation.  Hence `L` has value `(y)⁻¹ (x)⁻¹`, where `x`, `y` are the labels of `d`
   and `φ d`.
3. *Two short legal words* (`TriangleConnector`): `[x, x⁻¹]` has the value `1` of the empty word,
   and `[y⁻¹, x⁻¹]` has the value of `L`.  They are legal in the symmetric label alphabet, have
   length `2 ≤ ε`, and have norm at most their length.
4. *A quadrilateral walk* (`false_of_triangle_walk`).  One of `o`, `o′` is a cell `i`.
   * If `o = some i`, the walk `φ d, L, d` (rotation `r + 1`) is `[] ++ [φ d] ++ L ++ [d]`.  The
     source arc is the single dart `α d` of cell `i`, and the target arc is the single dart
     `α (φ d)` of `o′`.
   * If `o = none` and `o′ = some j`, the walk `L, d, φ d` (rotation `r + 2`) is
     `L ++ [d] ++ [] ++ [φ d]`.  The source arc is `α (φ d)` on cell `j`, and the target arc is
     `d` on the outer boundary.
   A single outer dart lies inside one section (`exists_section_of_lt`), and the target differs
   from the source.  The face `F` is not the outer face, no relator cell, and lies in no
   selected region.  So `RealizedSectionFamily.false_of_quadrilateral_face` gives a new region
   against the weight maximality of `S`.

## Manuscript status

Infrastructure for `thm:hull` (through Osin's Lemma 9.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate

section TriangleCornerLists

/-- A dart of a cycle is a cyclic arc of length one. -/
theorem exists_singleArc {Dart : Type v} {cycle : List Dart} {a : Dart} (ha : a ∈ cycle) :
    ∃ arc : CyclicArc cycle, arc.darts = [a] ∧ arc.length = 1 ∧ arc.start.1 < cycle.length := by
  obtain ⟨n, hn, hna⟩ := List.getElem_of_mem ha
  have e : cycle.drop n ++ cycle.take n = a :: (cycle.drop (n + 1) ++ cycle.take n) := by
    rw [List.drop_eq_getElem_cons hn, hna, List.cons_append]
  exact ⟨⟨⟨n, by omega⟩, 1, by omega⟩, (congrArg (List.take 1) e).trans rfl, rfl, hn⟩

/-- A cyclic arc on the single dart `α a` has the reversed boundary `[a]`. -/
theorem reverseDarts_eq_singleton {M : CombMap} {cycle : List M.Dart} (arc : CyclicArc cycle)
    {a : M.Dart} (h : arc.darts = [M.alpha a]) : arc.reverseDarts = [a] := by
  rw [CyclicArc.reverseDarts, h]
  exact congrArg (fun z => [z]) (M.alpha_involutive a)

/-- Rotating one step further moves the head to the end. -/
theorem rotate_succ_of_rotate_eq {α : Type*} {l : List α} {r : ℕ} {a : α} {tl : List α}
    (h : l.rotate r = a :: tl) : l.rotate (r + 1) = tl ++ [a] := by
  have e : (a :: tl).rotate 1 = tl ++ [a] := by
    have h1 := List.rotate_cons_succ tl a 0
    rwa [List.rotate_zero] at h1
  rw [← List.rotate_rotate, h, e]

/-- A position of the boundary word lies inside one section. -/
theorem exists_section_of_lt {G : Type u} [Group G] {Lambda : Type w} {D : RelGenSet G Lambda}
    {lambda c : ℝ} {word : List (RelLetter G Lambda)} (cs : SectionCuts D lambda c word) {p : ℕ}
    (hp : p < word.length) :
    ∃ j : Fin cs.count, cs.cut j.castSucc ≤ p ∧ p + 1 ≤ cs.cut j.succ := by
  classical
  have hex : ∃ n : ℕ, ∃ h : n < cs.count + 1, p < cs.cut ⟨n, h⟩ :=
    ⟨cs.count, Nat.lt_succ_self _, lt_of_lt_of_eq hp cs.cut_last.symm⟩
  obtain ⟨hn, hpn⟩ := Nat.find_spec hex
  have hn0 : Nat.find hex ≠ 0 := by
    intro h0
    have e : (⟨Nat.find hex, hn⟩ : Fin (cs.count + 1)) = 0 := Fin.ext (by simp [h0])
    rw [e, cs.cut_zero] at hpn
    exact Nat.not_lt_zero _ hpn
  have hlt : Nat.find hex - 1 < cs.count := by omega
  refine ⟨⟨Nat.find hex - 1, hlt⟩, ?_, ?_⟩
  · by_contra hcon
    rw [not_le] at hcon
    exact Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega) ⟨by omega, hcon⟩
  · have hsucc : (⟨Nat.find hex - 1, hlt⟩ : Fin cs.count).succ = ⟨Nat.find hex, hn⟩ :=
      Fin.ext (by simp only [Fin.val_succ]; omega)
    rw [hsucc]
    exact hpn

/-- **A corner of a face walk.**  A dart `d` of a face with `φ d ≠ d` starts a rotation of the
walk that reads `d, φ d, …`. -/
theorem exists_rotate_corner {M : CombMap} {f : M.Face} (B : FaceBoundary M f) {d : M.Dart}
    (hd : d ∈ B.darts) (hfix : M.facePerm d ≠ d) :
    ∃ (r : ℕ) (L : List M.Dart), r ≤ B.darts.length ∧
      B.darts.rotate r = d :: M.facePerm d :: L := by
  obtain ⟨n, hn, hnd⟩ := List.getElem_of_mem hd
  have hrot : B.darts.rotate n = d :: (B.darts.drop (n + 1) ++ B.darts.take n) := by
    rw [List.rotate_eq_drop_append_take hn.le, List.drop_eq_getElem_cons hn, hnd, List.cons_append]
  have key : ∀ (l T : List M.Dart), l = d :: T → l.IsChain (fun x y => M.facePerm x = y) →
      (∀ h : l ≠ [], M.facePerm (l.getLast h) = l.head h) → ∃ L, l = d :: M.facePerm d :: L := by
    rintro l T rfl hch hcl
    cases T with
    | nil => exact absurd (hcl (List.cons_ne_nil _ _)) hfix
    | cons e L =>
      have h1 : M.facePerm d = e := (List.isChain_cons_cons.mp hch).1
      exact ⟨L, congrArg (fun z => d :: z :: L) h1.symm⟩
  obtain ⟨L, hL⟩ := key _ _ hrot
    (Embedded.isChain_rotate_of_isChain_closes B.nonempty B.chain B.closes n)
    (Embedded.isChain_rotate_closing B.nonempty B.chain B.closes n)
  exact ⟨n, L, hn.le, hL⟩

end TriangleCornerLists

-- TRIANGLE_CORNER_PART_TWO
