import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkInnerKindCount
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkOuterKindCount
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkEulerSectorFree
import GroupApproximation.Meta.AxiomGuard

/-!
# The vertex bound for a noncrossing closed walk whose passages have free sectors

Osin, arXiv:math/0411039v3, proof of Lemma 9.7(b): "Let us consider the subdiagram `Γ_1` of `Δ`
such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2` ... (ii) `Γ_1` contains all `Γ_{i,1}`'s."

Let `w` be a noncrossing closed walk in a planar map whose passages have free sectors.  The inner
reclosing has one vertex for each vertex without adjacent passage carrying a retained inner dart and
one for each adjacent passage (`IsNoncrossingClosedWalk.inner_vertexCount_kind`); the outer reclosing
has one vertex for each untouched or adjacent vertex carrying a retained outer dart and one for each
passage that is not adjacent (`IsNoncrossingClosedWalk.outer_vertexCount_kind`).  The passages give
`|w|` together.  Every vertex is counted at least once: a vertex with an adjacent passage carries the
retained outer dart `w[l+1]`, a touched vertex carries the retained inner dart `alpha w[l]`, and an
untouched vertex has a dart that is not internal to both sides.

* `IsNoncrossingClosedWalk.kinds_of_vertex`, `IsNoncrossingClosedWalk.vertexCount_le_kinds`.
* `IsNoncrossingClosedWalk.card_passageAdjacent_add`.
* `sectorFreeVertexCount : SectorFreeVertexCountStatement`, which discharges the named residual of
  `NoncrossingClosedWalkEulerSectorFree`.
* `IsNoncrossingClosedWalk.eulers_of_passageSectorFree`: both reclosings keep the Euler characteristic.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(b);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv Surgery.MapCollapse SimpleClosedWalkSides SectorNoninterleaving NoncrossingClosedWalkEuler

universe u

namespace IsNoncrossingClosedWalk

variable {M : CombMap.{u}} {w : List M.Dart}

/-- **A vertex that is not an outer kind is an inner kind.** -/
theorem kinds_of_vertex (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar) (c : M.Vertex)
    (h : ¬ ((¬ Touched M w c ∨ AdjVertex M w c) ∧
      ∃ x : KeptDart M (sideOutside M w), M.vertexOf x.1 = c)) :
    ¬ AdjVertex M w c ∧ ∃ x : KeptDart M (sideFaces M w), M.vertexOf x.1 = c := by
  have hA : ¬ AdjVertex M w c := by
    rintro ⟨i, hi, hadj⟩
    exact h ⟨Or.inr ⟨i, hi, hadj⟩, ⟨w.get (finRotate w.length i), fun hint =>
      (mem_sideOutside_iff M w _).mp hint.1
        ((hw.isBoundaryDart_sideFaces_iff hM _).mpr (List.get_mem w _)).1⟩,
      (get_finRotate_of_isChain_closes hw.ne_nil hw.chain hw.closes i).symm.trans hi⟩
  refine ⟨hA, ?_⟩
  by_cases hT : Touched M w c
  · obtain ⟨i, hi⟩ := hT
    exact ⟨⟨M.alpha (w.get i), fun hint =>
      hw.faceOf_alpha_not_mem_of_mem hM (List.get_mem w i) hint.1⟩, hi⟩
  · by_contra hin
    have hout : ¬ ∃ x : KeptDart M (sideOutside M w), M.vertexOf x.1 = c :=
      fun hex => h ⟨Or.inl hT, hex⟩
    have h1 := internal_of_not_exists (d := Quotient.out c) hin (Quotient.out_eq' c)
    have h2 := internal_of_not_exists (d := Quotient.out c) hout (Quotient.out_eq' c)
    exact (mem_sideOutside_iff M w _).mp h2.1 h1.1

/-- **Every vertex is an inner kind or an outer kind.** -/
theorem vertexCount_le_kinds (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar) :
    M.vertexCount ≤
      Nat.card {c : M.Vertex // ¬ AdjVertex M w c ∧
          ∃ x : KeptDart M (sideFaces M w), M.vertexOf x.1 = c} +
        Nat.card {c : M.Vertex // (¬ Touched M w c ∨ AdjVertex M w c) ∧
          ∃ x : KeptDart M (sideOutside M w), M.vertexOf x.1 = c} := by
  classical
  rw [CombMap.vertexCount, ← Nat.card_sum]
  refine Nat.card_le_card_of_surjective (Sum.elim (fun a => a.1) (fun b => b.1)) ?_
  intro c
  by_cases h : (¬ Touched M w c ∨ AdjVertex M w c) ∧
      ∃ x : KeptDart M (sideOutside M w), M.vertexOf x.1 = c
  · exact ⟨Sum.inr ⟨c, h⟩, rfl⟩
  · exact ⟨Sum.inl ⟨c, hw.kinds_of_vertex hM c h⟩, rfl⟩

/-- **The adjacent and the other passages make up the walk.** -/
theorem card_passageAdjacent_add (M : CombMap.{u}) (w : List M.Dart) :
    Nat.card {i : Fin w.length // PassageAdjacent M w i} +
      Nat.card {i : Fin w.length // ¬ PassageAdjacent M w i} = w.length := by
  classical
  rw [← Nat.card_sum,
    Nat.card_congr (Equiv.sumCompl fun i : Fin w.length => PassageAdjacent M w i),
    Nat.card_eq_fintype_card, Fintype.card_fin]

end IsNoncrossingClosedWalk

/-- **The vertex bound for a noncrossing walk whose passages have free sectors.** -/
theorem sectorFreeVertexCount : SectorFreeVertexCountStatement.{u} := by
  intro M hM w hw hsector
  rw [hw.inner_vertexCount_kind hM hsector, hw.outer_vertexCount_kind hM hsector, Nat.card_sum,
    Nat.card_sum]
  have hV := hw.vertexCount_le_kinds hM
  have hP := IsNoncrossingClosedWalk.card_passageAdjacent_add M w
  omega

namespace IsNoncrossingClosedWalk

variable {M : CombMap.{u}} {w : List M.Dart}

/-- **Both reclosings of a noncrossing closed walk whose passages have free sectors keep the Euler
characteristic.** -/
theorem eulers_of_passageSectorFree (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hsector : ∀ i : Fin w.length, PassageSectorFree M w (w.get i) (w.get (finRotate w.length i))) :
    (reclosedMap M (sideFaces M w) (hw.innerCycle hM)).eulerCharacteristic =
        M.eulerCharacteristic ∧
      (reclosedMap M (sideOutside M w) (hw.outerCycle hM)).eulerCharacteristic =
        M.eulerCharacteristic :=
  hw.eulers_of_sectorFree sectorFreeVertexCount hM hsector

end IsNoncrossingClosedWalk

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.kinds_of_vertex
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.vertexCount_le_kinds
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.card_passageAdjacent_add
#audit_closed_axioms GroupApproximation.GGT.VanKampen.sectorFreeVertexCount
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.eulers_of_passageSectorFree
