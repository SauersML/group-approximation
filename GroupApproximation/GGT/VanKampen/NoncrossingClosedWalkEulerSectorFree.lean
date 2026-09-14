import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkSectorNoninterleaving
import GroupApproximation.Meta.AxiomGuard

/-!
# Both reclosings of a noncrossing closed walk whose passages have free sectors

Osin, arXiv:math/0411039v3, proof of Lemma 9.7(b): "Let us consider the subdiagram `Γ_1` of `Δ`
such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2` ... (ii) `Γ_1` contains all `Γ_{i,1}`'s."

`IsNoncrossingClosedWalk.eulers_of_vertexCount_le` (`NoncrossingClosedWalkEulerNoninterleaving`) keeps
both Euler characteristics of the reclosings of a noncrossing closed walk once the two reclosings
together have at least `|w|` more vertices than the map.  The pocket walks have a stronger property
than non-interleaving: every passage has a free sector, either from `alpha w[i]` to `w[i+1]` or back
(`SectorNoninterleaving.PassageSectorFree`).  At a vertex the passages then all turn the short way, or
all the long way, and the vertex count splits into first-return orbits.

* `SectorFreeVertexCountStatement` (named residual, not proved here): the vertex bound for a noncrossing
  closed walk whose passages have free sectors.
* `sectorFreeVertexCount_of_noninterleaving`: the general bound `NoninterleavingVertexCountStatement`
  gives it, since free sectors make the passages non-interleaving.
* `IsNoncrossingClosedWalk.eulers_of_sectorFree`: both Euler equalities from the residual.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(b);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv Surgery.MapCollapse SimpleClosedWalkSides SectorNoninterleaving

universe u

/-- **The vertex bound for a noncrossing walk whose passages have free sectors** (named residual).
For a noncrossing closed walk in a planar map in which every passage has a free sector, the two
reclosings together have at least `|w|` more vertices than the map. -/
def SectorFreeVertexCountStatement : Prop :=
  ∀ (M : CombMap.{u}) (hM : M.IsPlanar) (w : List M.Dart) (hw : IsNoncrossingClosedWalk M w),
    (∀ i : Fin w.length, PassageSectorFree M w (w.get i) (w.get (finRotate w.length i))) →
      M.vertexCount + w.length ≤
        (reclosedMap M (sideFaces M w) (hw.innerCycle hM)).vertexCount +
          (reclosedMap M (sideOutside M w) (hw.outerCycle hM)).vertexCount

/-- The general vertex bound for non-interleaving passages gives the bound for free sectors. -/
theorem sectorFreeVertexCount_of_noninterleaving
    (h : NoninterleavingVertexCountStatement.{u}) : SectorFreeVertexCountStatement.{u} :=
  fun M hM w hw hsector => h M hM w hw (hw.passagesNoninterleaving hsector)

namespace IsNoncrossingClosedWalk

variable {M : CombMap.{u}} {w : List M.Dart}

/-- **Both reclosings of a noncrossing closed walk whose passages have free sectors keep the Euler
characteristic**, from the named vertex bound. -/
theorem eulers_of_sectorFree (hcount : SectorFreeVertexCountStatement.{u})
    (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hsector : ∀ i : Fin w.length, PassageSectorFree M w (w.get i) (w.get (finRotate w.length i))) :
    (reclosedMap M (sideFaces M w) (hw.innerCycle hM)).eulerCharacteristic =
        M.eulerCharacteristic ∧
      (reclosedMap M (sideOutside M w) (hw.outerCycle hM)).eulerCharacteristic =
        M.eulerCharacteristic :=
  hw.eulers_of_vertexCount_le hM (hcount M hM w hw hsector)

end IsNoncrossingClosedWalk

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.SectorFreeVertexCountStatement
#audit_axioms GroupApproximation.GGT.VanKampen.sectorFreeVertexCount_of_noninterleaving
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.eulers_of_sectorFree

