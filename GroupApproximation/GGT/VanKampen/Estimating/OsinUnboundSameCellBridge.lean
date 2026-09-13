import GroupApproximation.GGT.VanKampen.CombMapEulerUpperBound
import GroupApproximation.GGT.VanKampen.CombMapEdgeInsertion
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSameCellPocket
import GroupApproximation.Meta.AxiomGuard

/-!
# Same-cell unbound darts: the edge is a bridge

On a planar map, an edge with the same face on both sides is a bridge.  No sequence of vertex
rotations and reversals at other edges joins its two darts.

The proof deletes the edge.
* A degree-one endpoint is alone in its class of moves.
* Otherwise the deletion keeps every vertex, and `EdgeDeletion.euler_balance_of_sameFace` raises
  the Euler characteristic to four.
* If the two darts were joined without the edge, the deleted map would be connected.  That
  contradicts `CombMap.eulerCharacteristic_le_two`.
-/

namespace GroupApproximation.GGT.VanKampen

universe u

/-- **A fixed endpoint is alone.**  A dart of the edge of `d` that vertex rotation fixes is alone
in its class of moves that avoid the edge. -/
theorem AvoidEdgeStep.eq_iff_of_sigma_fixed {M : CombMap} {d b : M.Dart}
    (hb : b = d ∨ b = M.alpha d) (hfix : M.sigma b = b) {x y : M.Dart}
    (h : Relation.EqvGen (AvoidEdgeStep M d) x y) : x = b ↔ y = b := by
  induction h with
  | rel x y h =>
      rcases h with h | ⟨hxd, hxa, h⟩
      · exact ⟨fun hx => h.symm.trans (by rw [hx]; exact hfix),
          fun hy => M.sigma.injective (h.trans (hy.trans hfix.symm))⟩
      · refine iff_of_false (fun hx => ?_) (fun hy => ?_)
        · rcases hb with hb | hb
          · exact hxd (hx.trans hb)
          · exact hxa (hx.trans hb)
        · rcases hb with hb | hb
          · exact hxa ((M.alpha_involutive x).symm.trans
              (congrArg M.alpha (h.trans (hy.trans hb))))
          · exact hxd (M.alpha.injective (h.trans (hy.trans hb)))
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **A same-face edge is a bridge.**  On a planar map, if both darts of an edge lie on one face,
no sequence of moves that avoid the edge joins them. -/
theorem AvoidEdgeStep.not_eqvGen_alpha_of_sameFace (M : CombMap.{u}) (hM : M.IsPlanar)
    (a : M.Dart) (hface : M.faceOf a = M.faceOf (M.alpha a)) :
    ¬ Relation.EqvGen (AvoidEdgeStep M a) a (M.alpha a) := by
  classical
  intro hreach
  by_cases ha : M.sigma a = a
  · exact M.alpha_fixedPointFree a
      ((AvoidEdgeStep.eq_iff_of_sigma_fixed (d := a) (b := a) (Or.inl rfl) ha hreach).mp rfl)
  by_cases hb : M.sigma (M.alpha a) = M.alpha a
  · exact M.alpha_fixedPointFree a
      ((AvoidEdgeStep.eq_iff_of_sigma_fixed (d := a) (b := M.alpha a) (Or.inr rfl) hb
        hreach).mpr rfl).symm
  have hcycle : M.facePerm.SameCycle a (M.alpha a) := (M.faceOf_eq_iff a (M.alpha a)).mp hface
  -- Neither endpoint is swapped onto the other: that would put `a` or `α a` alone on its face.
  have hsa : M.sigma a ≠ M.alpha a := by
    intro hsa
    have hfix : M.facePerm (M.alpha a) = M.alpha a := by
      change M.sigma (M.alpha (M.alpha a)) = M.alpha a
      rw [M.alpha_involutive]
      exact hsa
    exact M.alpha_fixedPointFree a (hcycle.symm.eq_of_left hfix)
  have hsb : M.sigma (M.alpha a) ≠ a := by
    intro hsb
    have hfix : M.facePerm a = a := hsb
    exact M.alpha_fixedPointFree a (hcycle.eq_of_left hfix).symm
  -- Every elementary move of the old map is joined by moves that avoid the edge.
  have hall (x y : M.Dart) : Relation.EqvGen (AvoidEdgeStep M a) x y := by
    have h := hM.1 x y
    induction h with
    | rel x y h =>
        rcases h with h | h
        · by_cases hxa : x = a
          · rw [← h, hxa]
            exact hreach
          · by_cases hxb : x = M.alpha a
            · rw [← h, hxb, M.alpha_involutive]
              exact hreach.symm
            · exact Relation.EqvGen.rel x y (Or.inr ⟨hxa, hxb, h⟩)
        · exact Relation.EqvGen.rel x y (Or.inl h)
    | refl x => exact Relation.EqvGen.refl x
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih₁ ih₂ => exact Relation.EqvGen.trans x y z ih₁ ih₂
  -- Send the two deleted darts to retained darts at their vertices.
  obtain ⟨ca, hca⟩ : ∃ ca : (EdgeDeletion.toCombMap M a).Dart,
      M.vertexOf (EdgeDeletion.value M a ca) = M.vertexOf a :=
    ⟨EdgeDeletion.ofValue M a (M.sigma a) ha hsa, M.vertexOf_sigma a⟩
  obtain ⟨cb, hcb⟩ : ∃ cb : (EdgeDeletion.toCombMap M a).Dart,
      M.vertexOf (EdgeDeletion.value M a cb) = M.vertexOf (M.alpha a) :=
    ⟨EdgeDeletion.ofValue M a (M.sigma (M.alpha a)) hsb hb, M.vertexOf_sigma (M.alpha a)⟩
  let collapse : M.Dart → (EdgeDeletion.toCombMap M a).Dart := fun z =>
    if hz : z = a then ca else if hz' : z = M.alpha a then cb
      else EdgeDeletion.ofValue M a z hz hz'
  have hval (z : M.Dart) (hz : z ≠ a) (hz' : z ≠ M.alpha a) :
      collapse z = EdgeDeletion.ofValue M a z hz hz' := by
    simp only [collapse, dif_neg hz, dif_neg hz']
  have hself (d : (EdgeDeletion.toCombMap M a).Dart) :
      collapse (EdgeDeletion.value M a d) = d :=
    (hval _ (EdgeDeletion.value_ne M a d) (EdgeDeletion.value_ne_reverse M a d)).trans
      (EdgeDeletion.value_injective M a rfl)
  have hvert (z : M.Dart) : M.vertexOf (EdgeDeletion.value M a (collapse z)) = M.vertexOf z := by
    by_cases hz : z = a
    · have hc : collapse z = ca := by simp only [collapse, dif_pos hz]
      rw [hc, hz]
      exact hca
    · by_cases hz' : z = M.alpha a
      · have hc : collapse z = cb := by simp only [collapse, dif_neg hz, dif_pos hz']
        rw [hc, hz']
        exact hcb
      · exact congrArg (fun w => M.vertexOf (EdgeDeletion.value M a w)) (hval z hz hz')
  -- Moves that avoid the edge become moves of the deleted map.
  have hlift (x y : M.Dart) (h : Relation.EqvGen (AvoidEdgeStep M a) x y) :
      Relation.EqvGen (EdgeDeletion.toCombMap M a).Adjacent (collapse x) (collapse y) := by
    induction h with
    | rel x y h =>
        rcases h with h | ⟨hxa, hxb, h⟩
        · apply CombMap.eqvGen_of_sameCycle_sigma
          rw [← CombMap.vertexOf_eq_iff, EdgeDeletion.vertexOf_eq_iff, hvert, hvert, ← h,
            M.vertexOf_sigma]
        · have hya : M.alpha x ≠ a := fun h' =>
            hxb ((M.alpha_involutive x).symm.trans (congrArg M.alpha h'))
          have hyb : M.alpha x ≠ M.alpha a := fun h' => hxa (M.alpha.injective h')
          rw [← h, hval x hxa hxb, hval (M.alpha x) hya hyb]
          exact Relation.EqvGen.rel _ _
            (Or.inl (EdgeDeletion.value_injective M a (EdgeDeletion.alpha_val M a _)))
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  have hN : (EdgeDeletion.toCombMap M a).IsConnected := by
    intro d e
    have hpath := hlift _ _ (hall (EdgeDeletion.value M a d) (EdgeDeletion.value M a e))
    rwa [hself d, hself e] at hpath
  -- The deletion keeps every vertex and raises the Euler characteristic to four.
  have hV : (EdgeDeletion.toCombMap M a).vertexCount = M.vertexCount :=
    EdgeDeletion.vertexCount_eq_of_sigma_ne M a hM.1 ca ha hb
  have hbal := EdgeDeletion.euler_balance_of_sameFace M a hface
  have hle := (EdgeDeletion.toCombMap M a).eulerCharacteristic_le_two hN
  have h2 : M.eulerCharacteristic = 2 := hM.2
  rw [hV] at hbal
  omega

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.AvoidEdgeStep.not_eqvGen_alpha_of_sameFace
