import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionPieces
import GroupApproximation.GGT.VanKampen.Estimating.PieceBridge
import GroupApproximation.GGT.VanKampen.Estimating.ShortSection
import GroupApproximation.GGT.VanKampen.GRegionBoundaryValue
import GroupApproximation.GGT.VanKampen.RelativeGreendlinger
import GroupApproximation.Meta.AxiomGuard

/-!
# Contiguity regions with an empty arc

`O52LeastAreaStatement` is proved by a surgery that deletes one shared edge on each
side of a contiguity region, so it needs both contiguity arcs nonempty.  A region with
an empty arc needs no O52.  By the region's own arc equation
(`ContiguityGeometry.arcs_value`) the other arc names a product of the two sides, of
norm at most `2ε`.  That arc is a prefix of a `(λ, c)`-quasi-geodesic relator rotation,
so its length is at most `λ⁻¹(2ε + c)`.

* `ContiguityGeometry.sourceArc_quasi_lower`, `ContiguityGeometry.targetBoundary_quasi_lower`:
  the quasi-geodesic lower bounds for both arcs of a region to a cell.
* `ContiguityGeometry.arcLengths_le_of_degenerate`:
  `l(q₁) + l(q₂) ≤ λ⁻¹(2ε + c)` when one arc is empty.
* `RegionCandidate.weight_le_of_degenerate`: the O52 charge `2μ l(∂Π)` at any cell,
  once `λ⁻¹(3ε + c) < (μ/2)ρ`.
-/

namespace GroupApproximation.GGT.VanKampen.Embedded

open GroupApproximation.HullSC GroupApproximation.WordMetric

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w}
  {D : GGT.RelGenSet G Lambda}
  {W : Set (List (GGT.RelLetter G Lambda))}
  {eps rho : ℕ} {mu lambda c : ℝ}
  {Delta : DiscDiagram.{u, w, v} W}
  {faces : Finset Delta.toCombMap.Face}

/-- A cast of a cyclic arc along an equality of carriers keeps its length. -/
theorem CyclicArc.length_cast {Dart : Type v} {l₁ l₂ : List Dart} (h : l₁ = l₂)
    (arc : CyclicArc l₁) : (cast (congrArg CyclicArc h) arc).length = arc.length := by
  subst h
  rfl

/-- An empty dart list names the identity. -/
theorem listVal_dartWord_of_length_eq_zero {l : List Delta.toCombMap.Dart}
    (h : l.length = 0) : RelLetter.listVal (dartWord Delta l) = 1 := by
  rw [List.eq_nil_of_length_eq_zero h]
  exact RelLetter.listVal_nil

namespace ContiguityGeometry

/-- The source arc is a prefix of a relator rotation, so its endpoint distance has the
quasi-geodesic lower bound. -/
theorem sourceArc_quasi_lower (Gamma : ContiguityGeometry D eps Delta faces)
    (hcondition : OsinCCondition D W eps mu lambda c rho) :
    lambda * (Gamma.sourceArc.length : ℝ) - c ≤
      (wordNorm D.alphabet.carrier
        (RelLetter.listVal (dartWord Delta Gamma.sourceArc.darts)) : ℝ) := by
  have hquasi := hcondition.quasiGeodesic _
    (Gamma.sourceArc.cell_rotated_mem hcondition.toIsSmallCancellation)
  have hlength : Gamma.sourceArc.length ≤
      (dartWord Delta Gamma.sourceArc.rotated).length := by
    simpa only [dartWord, List.length_map, Gamma.sourceArc.rotated_length]
      using Gamma.sourceArc.length_le
  have h := hquasi.2 0 Gamma.sourceArc.length (Nat.zero_le _) hlength
  have hprefix : (dartWord Delta Gamma.sourceArc.rotated).take
      Gamma.sourceArc.length = dartWord Delta Gamma.sourceArc.darts := by
    simp only [dartWord, CyclicArc.darts, List.map_take]
  simpa only [Nat.sub_zero, OsinComponents.vertex_zero,
    OsinComponents.vertex_eq_mul_listVal_take, one_mul, hprefix,
    List.take_zero, RelLetter.listVal_nil, wordDist_one_left] using h

/-- The oppositely oriented target boundary of a region to a cell inverts a prefix of a
relator rotation, so it has the quasi-geodesic lower bound. -/
theorem targetBoundary_quasi_lower (Gamma : ContiguityGeometry D eps Delta faces)
    (target : Fin Delta.rCellCount) (htarget : Gamma.target = some target)
    (hcondition : OsinCCondition D W eps mu lambda c rho) :
    lambda * (Gamma.targetArc.length : ℝ) - c ≤
      (wordNorm D.alphabet.carrier (RelLetter.listVal
        (dartWord Delta (targetBoundaryDarts Delta Gamma.target Gamma.targetArc))) : ℝ) := by
  obtain ⟨arcT, harcT⟩ : ∃ a : CyclicArc (cellDarts Delta target),
      a = Gamma.targetArcAtSome target htarget := ⟨_, rfl⟩
  have hlen : arcT.length = Gamma.targetArc.length :=
    (congrArg CyclicArc.length harcT).trans
      (CyclicArc.length_cast (congrArg (targetDarts Delta) htarget) Gamma.targetArc)
  have hquasi := hcondition.quasiGeodesic _
    (CyclicArc.cell_rotated_mem hcondition.toIsSmallCancellation arcT)
  have hlength : arcT.length ≤ (dartWord Delta arcT.rotated).length := by
    simpa only [dartWord, List.length_map, CyclicArc.rotated_length] using arcT.length_le
  have h := hquasi.2 0 arcT.length (Nat.zero_le _) hlength
  have hprefix : (dartWord Delta arcT.rotated).take arcT.length =
      dartWord Delta arcT.darts := by
    simp only [dartWord, CyclicArc.darts, List.map_take]
  have hlower : lambda * (arcT.length : ℝ) - c ≤
      (wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord Delta arcT.darts)) : ℝ) := by
    simpa only [Nat.sub_zero, OsinComponents.vertex_zero,
      OsinComponents.vertex_eq_mul_listVal_take, one_mul, hprefix,
      List.take_zero, RelLetter.listVal_nil, wordDist_one_left] using h
  have hboundary : targetBoundaryDarts Delta Gamma.target Gamma.targetArc =
      arcT.reverseDarts := by
    rw [harcT]
    exact targetBoundaryDarts_cast htarget Gamma.targetArc
  rw [hboundary, CyclicArc.reverseDarts, listVal_dartWord_reverse_alpha,
    wordNorm_inv D.alphabet.symmetricGenerating, ← hlen]
  exact hlower

/-- **An empty source arc**: the target boundary names a product of the two sides. -/
theorem targetBoundary_norm_le_of_sourceArc_empty
    (Gamma : ContiguityGeometry D eps Delta faces) (hs : Gamma.sourceArc.length = 0) :
    wordNorm D.alphabet.carrier (RelLetter.listVal
      (dartWord Delta (targetBoundaryDarts Delta Gamma.target Gamma.targetArc))) ≤
        2 * eps := by
  have hright := Gamma.rightSide_norm_le
  have hleft := Gamma.leftSide_norm_le
  have harcs := Gamma.arcs_value
  rw [listVal_dartWord_of_length_eq_zero (l := Gamma.sourceArc.darts)
    (by rw [CyclicArc.darts_length]; exact hs)] at harcs
  have hT : RelLetter.listVal
      (dartWord Delta (targetBoundaryDarts Delta Gamma.target Gamma.targetArc)) =
        (RelLetter.listVal (dartWord Delta Gamma.rightSide))⁻¹ *
          (RelLetter.listVal (dartWord Delta Gamma.leftSide))⁻¹ := by
    calc RelLetter.listVal
          (dartWord Delta (targetBoundaryDarts Delta Gamma.target Gamma.targetArc))
        = (RelLetter.listVal (dartWord Delta Gamma.rightSide))⁻¹ *
            (RelLetter.listVal (dartWord Delta Gamma.rightSide) *
              RelLetter.listVal
                (dartWord Delta (targetBoundaryDarts Delta Gamma.target Gamma.targetArc)) *
              RelLetter.listVal (dartWord Delta Gamma.leftSide)) *
            (RelLetter.listVal (dartWord Delta Gamma.leftSide))⁻¹ := by group
      _ = (RelLetter.listVal (dartWord Delta Gamma.rightSide))⁻¹ *
            (RelLetter.listVal (dartWord Delta Gamma.leftSide))⁻¹ := by
        rw [← harcs]
        group
  rw [hT]
  have h1 := wordNorm_mul_le D.alphabet.symmetricGenerating
    (RelLetter.listVal (dartWord Delta Gamma.rightSide))⁻¹
    (RelLetter.listVal (dartWord Delta Gamma.leftSide))⁻¹
  rw [wordNorm_inv D.alphabet.symmetricGenerating,
    wordNorm_inv D.alphabet.symmetricGenerating] at h1
  omega

/-- **An empty target arc**: the source arc names a product of the two sides. -/
theorem sourceArc_norm_le_of_targetArc_empty
    (Gamma : ContiguityGeometry D eps Delta faces) (ht : Gamma.targetArc.length = 0) :
    wordNorm D.alphabet.carrier
      (RelLetter.listVal (dartWord Delta Gamma.sourceArc.darts)) ≤ 2 * eps := by
  have hright := Gamma.rightSide_norm_le
  have hleft := Gamma.leftSide_norm_le
  have harcs := Gamma.arcs_value
  rw [listVal_dartWord_of_length_eq_zero
    (l := targetBoundaryDarts Delta Gamma.target Gamma.targetArc)
    (by rw [Gamma.targetBoundaryDarts_length]; exact ht), mul_one] at harcs
  rw [harcs]
  have h1 := wordNorm_mul_le D.alphabet.symmetricGenerating
    (RelLetter.listVal (dartWord Delta Gamma.rightSide))
    (RelLetter.listVal (dartWord Delta Gamma.leftSide))
  omega

/-- **A region with an empty arc needs no O52**: both arcs together have length at most
`λ⁻¹(2ε + c)`. -/
theorem arcLengths_le_of_degenerate (Gamma : ContiguityGeometry D eps Delta faces)
    (target : Fin Delta.rCellCount) (htarget : Gamma.target = some target)
    (hcondition : OsinCCondition D W eps mu lambda c rho) (hlambda : 0 < lambda)
    (hdeg : Gamma.sourceArc.length = 0 ∨ Gamma.targetArc.length = 0) :
    (Gamma.sourceArc.length : ℝ) + (Gamma.targetArc.length : ℝ) ≤
      lambda⁻¹ * (2 * (eps : ℝ) + c) := by
  rw [inv_mul_eq_div, le_div_iff₀ hlambda]
  rcases hdeg with hs | ht
  · have hnorm := Gamma.targetBoundary_norm_le_of_sourceArc_empty hs
    have hnormR : (wordNorm D.alphabet.carrier (RelLetter.listVal
        (dartWord Delta (targetBoundaryDarts Delta Gamma.target Gamma.targetArc))) : ℝ) ≤
          2 * (eps : ℝ) := by
      exact_mod_cast hnorm
    have hlower := Gamma.targetBoundary_quasi_lower target htarget hcondition
    rw [hs, Nat.cast_zero, zero_add]
    nlinarith
  · have hnorm := Gamma.sourceArc_norm_le_of_targetArc_empty ht
    have hnormR : (wordNorm D.alphabet.carrier
        (RelLetter.listVal (dartWord Delta Gamma.sourceArc.darts)) : ℝ) ≤
          2 * (eps : ℝ) := by
      exact_mod_cast hnorm
    have hlower := Gamma.sourceArc_quasi_lower hcondition
    rw [ht, Nat.cast_zero, add_zero]
    nlinarith

end ContiguityGeometry

namespace RegionCandidate

/-- **The charge of a region with an empty arc**, at any cell, from quasi-geodesicity
alone. -/
theorem weight_le_of_degenerate (a : RegionCandidate D eps Delta)
    (target : Fin Delta.rCellCount) (htarget : a.2.target = some target)
    (hcondition : OsinCCondition D W eps mu lambda c rho) (hlambda : 0 < lambda)
    (hmu : 0 < mu) (hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ))
    (hdeg : a.2.sourceArc.length = 0 ∨ a.2.targetArc.length = 0)
    (i : Fin Delta.rCellCount) :
    (a.weight : ℝ) ≤ 2 * mu * ((cell Delta i).word.length : ℝ) := by
  have hbound := a.2.arcLengths_le_of_degenerate target htarget hcondition hlambda hdeg
  have hmono : lambda⁻¹ * (2 * (eps : ℝ) + c) ≤ lambda⁻¹ * (3 * (eps : ℝ) + c) := by
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hlambda.le)
    have heps : (0 : ℝ) ≤ eps := Nat.cast_nonneg _
    linarith
  have hlong : (rho : ℝ) ≤ ((cell Delta i).word.length : ℝ) := by
    exact_mod_cast hcondition.long (cell Delta i).word (cell Delta i).word_mem
  have hmul : mu / 2 * (rho : ℝ) ≤ mu / 2 * ((cell Delta i).word.length : ℝ) :=
    mul_le_mul_of_nonneg_left hlong (by linarith)
  have hlen : (0 : ℝ) ≤ ((cell Delta i).word.length : ℝ) := Nat.cast_nonneg _
  rw [weight, Nat.cast_add]
  nlinarith

end RegionCandidate

end GroupApproximation.GGT.VanKampen.Embedded

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.ContiguityGeometry.targetBoundary_quasi_lower
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.ContiguityGeometry.arcLengths_le_of_degenerate
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.weight_le_of_degenerate
