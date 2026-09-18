import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixO52Collapse
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSections
import GroupApproximation.GGT.VanKampen.GRegionBoundaryValue
import GroupApproximation.Meta.AxiomGuard

/-!
# Two adjacent relator cells with trivial merged word

Lane gl-p10-79.  Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the cancellable-pair
exclusion at a least-area diagram.

## The map-level surgery

`roseLobeOsinPiece_relProd_sub_two`.  Let a planar van Kampen map carry two distinct
relator faces `Π`, `Σ` that share the edge `{a, α a}`, enumerated from it as the face cycles
`a :: xs` and `α a :: ys`.  Suppose `xs ++ ys` reads `1`.

* Both faces are relator faces, so neither is the outer face (`outer_not_mem`).
* If `xs ++ ys = []`, then `facePerm a = a` and `facePerm (α a) = α a`, so `σ` swaps `a` and
  `α a` (`sigma_eq_facePerm_alpha`).  The map is connected, so every dart is `a` or `α a`
  (`dart_eq_or_alpha_of_swapped_endpoints`), and the outer face is `Π` or `Σ`.  Contradiction.
* Otherwise delete the edge `a` (`EdgeDeletion.MergeCycles`).  `Π` and `Σ` merge into one face
  enumerated by `xs ++ ys`, which reads `1`.  `VanKampenData.exists_merge` at `P := False` makes
  it a trivial face, so the relator-face count drops by two.  The deleted map is planar
  (`planar_of_neFace`), and its outer face reads the same word.  The planar van Kampen lemma
  gives a relator product with `|relFaces| - 2` factors.

This is `VanKampenData.isRelatorProduct_sub_two` (VanKampenCancel) with the middle trivial face
removed: one merge instead of two.

## The least-area form

`roseLobeOsinPiece_merge_ne_one`.  In a least-area disc diagram `X`, take relator cells `i ≠ j`
whose faces share the edge `{a, α a}`, with `a` on cell `i`.  Then the merged word `xs ++ ys` is
not `1`.  Otherwise the boundary value is a product of `rCellCount - 2` relator conjugates
(the outer word is the inverse of the boundary word).  `LeastArea` gives
`rCellCount ≤ rCellCount - 2`, and `2 ≤ rCellCount` since `i ≠ j`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

universe u w v

open Embedded

/-- **Cancelling two adjacent relator faces.**  Two distinct relator faces sharing the edge
`{a, α a}`, whose merged word `xs ++ ys` reads `1`, can be removed: the outer word is a relator
product with two factors fewer. -/
theorem roseLobeOsinPiece_relProd_sub_two {G : Type u} [Group G] {Lambda : Type w}
    {R : Set G} {M : CombMap.{v}} [DecidableEq M.Dart] (hM : M.IsPlanar)
    {label : M.Dart → RelLetter G Lambda}
    (hlabel : ∀ d, label (M.alpha d) = HullSC.RelWord.inv (label d))
    (V : VanKampenData R M label) {a : M.Dart} {xs ys : List M.Dart}
    (cycP : M.IsFaceCycle (a :: xs)) (cycS : M.IsFaceCycle (M.alpha a :: ys))
    (hPrel : M.faceOf a ∈ V.relFaces) (hSrel : M.faceOf (M.alpha a) ∈ V.relFaces)
    (hPS : M.faceOf a ≠ M.faceOf (M.alpha a))
    (hval : RelLetter.listVal ((xs ++ ys).map label) = 1) :
    RelatorDefectBudget.IsRelatorProduct R (V.relFaces.card - 2)
      (RelLetter.listVal (V.outer.map label)) := by
  classical
  have hPO : M.faceOf a ≠ M.faceOf (V.outer.head V.outer_cycle.ne_nil) := fun h =>
    V.outer_not_mem ((congrArg (fun z => z ∈ V.relFaces) h).mp hPrel)
  have hSO : M.faceOf (M.alpha a) ≠ M.faceOf (V.outer.head V.outer_cycle.ne_nil) := fun h =>
    V.outer_not_mem ((congrArg (fun z => z ∈ V.relFaces) h).mp hSrel)
  obtain ⟨C, hCx, hCy⟩ : ∃ C : EdgeDeletion.MergeCycles M a, C.xs = xs ∧ C.ys = ys :=
    ⟨⟨xs, ys, cycP, cycS, hPS⟩, rfl, rfl⟩
  by_cases hne : C.xs ++ C.ys = []
  · -- the merged face would be empty: the edge `a` would carry the outer face
    exfalso
    have hxs : C.xs = [] := (List.append_eq_nil_iff.mp hne).1
    have hys : C.ys = [] := (List.append_eq_nil_iff.mp hne).2
    have hfa : M.facePerm a = a := by
      have h := C.facePerm_getD_last_xs
      rw [hxs] at h
      exact h
    have hfαa : M.facePerm (M.alpha a) = M.alpha a := by
      have h := C.facePerm_getD_last_ys
      rw [hys] at h
      exact h
    have hσa : M.sigma a = M.alpha a := by
      rw [M.sigma_eq_facePerm_alpha, hfαa]
    have hσαa : M.sigma (M.alpha a) = a := by
      rw [M.sigma_eq_facePerm_alpha, M.alpha_involutive, hfa]
    rcases M.dart_eq_or_alpha_of_swapped_endpoints hM.1 a hσa hσαa
        (V.outer.head V.outer_cycle.ne_nil) with h | h
    · exact hPO (congrArg M.faceOf h.symm)
    · exact hSO (congrArg M.faceOf h.symm)
  -- the merge along `a`
  obtain ⟨l, hl⟩ := EdgeDeletion.exists_map_value_eq M a (C.xs ++ C.ys)
    fun d hd => C.avoid hd
  have hlne : l ≠ [] := by
    rintro rfl
    exact hne hl.symm
  have htrivF : RelLetter.listVal ((C.xs ++ C.ys).map label) = 1 := by
    rw [hCx, hCy]
    exact hval
  obtain ⟨V', hV'outer, _, hV'card⟩ := V.exists_merge C hne hl hlne hPO hSO False
    (fun h => h.elim) (fun _ => htrivF)
  have hcard : V'.relFaces.card + 2 = V.relFaces.card := by
    simp only [if_pos hPrel, if_pos hSrel, if_neg not_false] at hV'card
    omega
  have hNplanar := EdgeDeletion.planar_of_neFace M a hM (l.head hlne) C.face_ne
  have hprod := V'.isRelatorProduct hNplanar (fun e => by
    show label (EdgeDeletion.value M a (EdgeDeletion.alpha M a e)) = _
    rw [EdgeDeletion.alpha_val, hlabel])
  have hmapO : RelLetter.listVal (V'.outer.map fun e => label (EdgeDeletion.value M a e)) =
      RelLetter.listVal (V.outer.map label) :=
    congrArg RelLetter.listVal ((List.map_map (g := label) (f := EdgeDeletion.value M a)
      (l := V'.outer)).symm.trans (congrArg (List.map label) hV'outer))
  rw [show V.relFaces.card - 2 = V'.relFaces.card by omega, ← hmapO]
  exact hprod

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinPiece_relProd_sub_two
