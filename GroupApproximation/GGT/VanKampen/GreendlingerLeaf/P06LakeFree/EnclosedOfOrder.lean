import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.EnclosedOrder
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Statement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketLakeFill
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.NormalForm
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.ArcSubInv
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P06, Route B: the lake-free enclosed face set from the planar order

Lane gl-p06-08 of `carto-gl-p06`.  Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b):

> "Let us consider the subdiagram `Γ_1` of `Δ` such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2`, where
> `s_1, s_2` are side arcs of some of `Γ_{i,1}`'s and `t_1, t_2` are subpaths of `∂Π` and the
> section `q_1` of `∂Δ`, respectively; (ii) `Γ_1` contains all `Γ_{i,1}`'s."

## Endpoint

`cellPocketFaceSetLakeFreeEnclosed_of_order`:
`CellPocketLakeFreeEnclosedOrderStatement → CellPocketFaceSetLakeFreeEnclosedStatement`.
The truth check and the full paper proof are in the docstring of `EnclosedOrder.lean`.

## Proof

Let `L` be the walk of the order statement: noncrossing, `C.face ∈ sideFaces L ⊆ K.faces`.
1. `o ∉ sideFaces L`, since `o ∉ K.faces`.  Fill the lakes
   (`P07InnerPocket.exists_lakeFill_of_noncrossing`): an outer walk `W` with
   `EnclosedFaceSetSucc X F W`, `F = absorbed (sideFaces L) o`, `C.face ∈ F`, and the dart
   description of `W`.
2. The order statement at `W` gives `n`, pieces `q₁` of `invDarts A(Π_i)`, `q₂` of
   `invDarts A(Π_j)`, sub-lists `s₁' <+ s₁`, `s₂' <+ s₂` and
   `invDarts (W.rotate n) = s₁' ++ q₁ ++ s₂' ++ q₂`.
3. `q₁ = invDarts B₁`, `q₂ = invDarts B₂` for arcs `B₁` of `Π_i`, `B₂` of `Π_j`
   (`P07InnerPocket.CyclicArc.exists_subArc_of_invDarts`).
4. `F ⊆ K.faces` (`enclosed_absorbed_subset_of_lakeFree`), so `Π_i`, `Π_j` are off `F`.
5. `|s_t'| ≤ |s_t| ≤ ε` (`List.Sublist.length_le`).
6. `P07InnerPocket.enclosedNormalForm` at `W.rotate n` (`EnclosedFaceSetSucc.rotate`), with
   `k₀ = i`, gives the verbatim conclusion.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **Lane gl-p06-08: the lake-free enclosed face set from the planar order.**  The planar order of
a lake-free pocket petal (`CellPocketLakeFreeEnclosedOrderStatement`) gives the enclosed two-arc
face set of `CellPocketFaceSetLakeFreeEnclosedStatement`: fill the lakes of the petal, keep the
cells outside by lake freeness, cut the arc pieces into arcs, bound the sides by sub-lists, rotate
and normalise (`P07InnerPocket.enclosedNormalForm`). -/
theorem cellPocketFaceSetLakeFreeEnclosed_of_order
    (h : CellPocketLakeFreeEnclosedOrderStatement.{u, w, v}) :
    CellPocketFaceSetLakeFreeEnclosedStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j K hij hlabel hW hw hfree C hC hCK
  obtain ⟨L, hL, hCL, hsub, hord⟩ := h D eps X K hij hlabel hW hw hfree C hC hCK
  have hout : X.outerFace ∉ sideFaces X.toCombMap L := fun hin => K.outerFace_not_mem (hsub hin)
  obtain ⟨ow, E, hCF, hmem⟩ := P07InnerPocket.exists_lakeFill_of_noncrossing X hL hout hCL
  obtain ⟨n, p₁, q₁, r₁, p₂, q₂, r₂, s₁, s₂, h₁, h₂, hs₁, hs₂, hdec⟩ := hord ow E hmem
  obtain ⟨B₁, hB₁⟩ := P07InnerPocket.CyclicArc.exists_subArc_of_invDarts K.firstArc h₁
  obtain ⟨B₂, hB₂⟩ := P07InnerPocket.CyclicArc.exists_subArc_of_invDarts K.secondArc h₂
  have hFK : ExteriorComponent.absorbed X.toCombMap (sideFaces X.toCombMap L) X.outerFace ⊆
      K.faces :=
    enclosed_absorbed_subset_of_lakeFree hfree hsub
  have hdec' : invDarts X (ow.rotate n) =
      s₁ ++ invDarts X B₁.darts ++ s₂ ++ invDarts X B₂.darts := by
    rw [hB₁, hB₂]
    exact hdec
  exact P07InnerPocket.enclosedNormalForm eps X _ (ow.rotate n)
    (P07InnerPocket.EnclosedFaceSetSucc.rotate E n) C hC hCF i i j B₁ B₂ s₁ s₂ hdec'
    (fun _ hin => K.first_not_mem (hFK hin)) (fun _ hin => K.second_not_mem (hFK hin))
    (fun hin => K.first_not_mem (hFK hin))
    (hs₁.length_le.trans K.firstSide_length_le) (hs₂.length_le.trans K.secondSide_length_le)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.cellPocketFaceSetLakeFreeEnclosed_of_order
