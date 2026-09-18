import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.Rotation
import GroupApproximation.Meta.AxiomGuard

/-!
# Opening a cell hair preserves a clean two-gon

Target: `GroupApproximation.GGT.VanKampen.TwoGonCellHairStepStatement`.

Mathematical proof. Let `S` be a distinguished family on a least-area diagram, `f` a relator
cell face with a hair corner `w = w_j`, and assume that neither `f` nor the face of `alpha w`
lies in any region of `S`. Opening the hair inserts a new edge `{none, some none}` between
`w` and its second corner; old darts enter through `embed z = some (some z)`.

(1) Transport. Every region `r ∈ S.family` goes to `r' := regionCandidate r` with the same
  target profile, the cells renumbered by `indexEquiv`, and crossings
  `crossO r' s o = (crossO r s o).map embed` (`transport`, module `Doubling`).
(2) `Φ'_M` is carried at every component. The collapsed maps are related by
  `ιc x = ⟨embed x, _⟩`, which commutes with `alpha` and misses `some none`; the dart `w`
  is not a crossing, since it lies on `f`, which belongs to no region and is not a crossing of
  a relator cell arc by `havoid`. The collapsed face rotation of the new map agrees with the old
  one along `ιc` away from `w`, sends the predecessor of `w` to `some none`, and sends
  `some none` to `ιc (facePerm w)`. Face-class paths are named back through `backDart`, and
  a relator cell face met on the new side is the face image of an old relator cell face,
  never the new digon. This is `phiTransportAt_hair` (module `Rotation`).
(3) `hasCleanTwoGon_of_transport` carries loops, multiple edges, the two-gon, the gap-holding
  corners and the holding cells along the transport, so `HasCleanTwoGon S` gives
  `HasCleanTwoGon (HairOpening.sectionFamily S f j hlen hf havoid)`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair

universe u w v

/-- **Opening a cell hair preserves a clean two-gon.** -/
theorem proof : TwoGonCellHairStepStatement.{u, w, v} := by
  intro G _ Lambda W D lambda c eps Delta cuts hlea S f j hlen hf havoid h
  exact hasCleanTwoGon_of_transport hlea (transport S f j hlen hf havoid)
    (fun a₀ => phiTransportAt_hair S f j hlen hf havoid a₀) h

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.proof
