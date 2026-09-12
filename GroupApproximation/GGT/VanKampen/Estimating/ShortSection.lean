import GroupApproximation.GGT.VanKampen.Estimating.Lemma65Statement
import GroupApproximation.GGT.OsinTheorem54SepPolygon
import GroupApproximation.Meta.AxiomGuard

/-!
# Contiguity to a short admissible boundary section

This is the metric step in Osin's Appendix Lemma 9.6(a). The rotated source
relator is quasi-geodesic; the pasted region gives a path between its arc
endpoints through the two connectors and the target. For a section of length
at most epsilon, that path has word norm at most `3 * epsilon`.

Admissibility of the section is explicit. It follows from a genuine boundary
section's quasi-geodesicity; an arbitrary list of ambient diagram darts need
not have labels in the relative alphabet.
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

/-- The source arc is a prefix of an actual relator rotation, so its endpoint
distance has the original multiplicative and additive lower bound. -/
theorem Contiguity.sourceArc_quasi_lower
    (Gamma : Contiguity D eps Delta faces)
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

/-- The pasted region bounds the norm of its source arc by the target norm
plus its two short connectors. -/
theorem Contiguity.sourceArc_norm_le
    (Gamma : Contiguity D eps Delta faces) :
    wordNorm D.alphabet.carrier
        (RelLetter.listVal (dartWord Delta Gamma.sourceArc.darts)) ≤
      2 * eps + wordNorm D.alphabet.carrier
        (RelLetter.listVal
          (dartWord Delta (targetBoundaryDarts Delta Gamma.target Gamma.targetArc))) := by
  obtain ⟨l, hshell⟩ := Gamma.pasting
  have heq := Gamma.arcs_value_of_pasting (faceSetWordHomotopy_of_shelling hshell)
  rw [heq]
  have hfirst := wordNorm_mul_le D.alphabet.symmetricGenerating
    (RelLetter.listVal (dartWord Delta Gamma.rightSide))
    (RelLetter.listVal
      (dartWord Delta (targetBoundaryDarts Delta Gamma.target Gamma.targetArc)))
  have hlast := wordNorm_mul_le D.alphabet.symmetricGenerating
    (RelLetter.listVal (dartWord Delta Gamma.rightSide) *
      RelLetter.listVal
        (dartWord Delta (targetBoundaryDarts Delta Gamma.target Gamma.targetArc)))
    (RelLetter.listVal (dartWord Delta Gamma.leftSide))
  have hright := Gamma.rightSide_norm_le
  have hleft := Gamma.leftSide_norm_le
  omega

/-- A boundary-target arc included in a short admissible section has norm at
most epsilon. Duplicate-free target darts justify the length comparison even
though `TargetsSection` is expressed as containment. -/
theorem Contiguity.targetArc_norm_le_of_shortSection
    (Gamma : Contiguity D eps Delta faces)
    (q : List Delta.toCombMap.Dart)
    (htarget : Gamma.TargetsSection q)
    (hadmissible : RelWord.IsAdmissible D (dartWord Delta q))
    (hshort : q.length ≤ eps) :
    wordNorm D.alphabet.carrier
        (RelLetter.listVal
          (dartWord Delta (targetBoundaryDarts Delta Gamma.target Gamma.targetArc))) ≤
      eps := by
  have hboundary : targetBoundaryDarts Delta Gamma.target Gamma.targetArc =
      Gamma.targetArc.darts := by
    exact (show ∀ (target : Option (Fin Delta.rCellCount))
        (arc : CyclicArc (targetDarts Delta target)), target = none →
          targetBoundaryDarts Delta target arc = arc.darts from by
      intro target arc h
      cases target with
      | none => rfl
      | some i => cases h) _ _ htarget.1
  have hnodup : Gamma.targetArc.darts.Nodup := by
    apply Gamma.targetArc.darts_nodup
    rw [htarget.1]
    exact List.Nodup.map Delta.toCombMap.alpha.injective
      (List.nodup_reverse.mpr (Delta.faceBoundary Delta.outerFace).nodup)
  have hlength : Gamma.targetArc.darts.length ≤ q.length :=
    (hnodup.subperm htarget.2).length_le
  rw [hboundary]
  have hnorm := OsinComponents.wordNorm_listVal_le D
    (dartWord Delta Gamma.targetArc.darts) (by
      intro letter hletter
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hletter
      exact hadmissible _ (List.mem_map.mpr ⟨d, htarget.2 d hd, rfl⟩))
  have hnorm' : wordNorm D.alphabet.carrier
      (RelLetter.listVal (dartWord Delta Gamma.targetArc.darts)) ≤
        Gamma.targetArc.darts.length := by
    simpa only [dartWord, List.length_map] using hnorm
  exact hnorm'.trans (hlength.trans hshort)

/-- Osin's source-arc length estimate, with the actual alphabet hypothesis
provided by a boundary section. No geometric estimate remains as an input. -/
theorem Contiguity.sourceArc_length_le_of_shortSection
    (Gamma : Contiguity D eps Delta faces)
    (q : List Delta.toCombMap.Dart)
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hlambda : 0 < lambda)
    (htarget : Gamma.TargetsSection q)
    (hadmissible : RelWord.IsAdmissible D (dartWord Delta q))
    (hshort : q.length ≤ eps) :
    (Gamma.sourceArc.length : ℝ) ≤ lambda⁻¹ * (3 * (eps : ℝ) + c) := by
  have hnorm := Gamma.sourceArc_norm_le
  have htargetNorm := Gamma.targetArc_norm_le_of_shortSection q htarget hadmissible hshort
  have hupper : (wordNorm D.alphabet.carrier
      (RelLetter.listVal (dartWord Delta Gamma.sourceArc.darts)) : ℝ) ≤
      3 * (eps : ℝ) := by
    exact_mod_cast (show wordNorm D.alphabet.carrier
      (RelLetter.listVal (dartWord Delta Gamma.sourceArc.darts)) ≤ 3 * eps by omega)
  have hlower := Gamma.sourceArc_quasi_lower hcondition
  rw [inv_mul_eq_div, le_div_iff₀ hlambda]
  nlinarith

/-- On the actual short sections used in the induction, admissibility is
already a field of the quasi-geodesic boundary decomposition. -/
theorem Contiguity.sourceArc_length_le_of_boundarySection
    (Gamma : Contiguity D eps Delta faces)
    (sections : BoundarySections D lambda c Delta) (j : Fin sections.count)
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hlambda : 0 < lambda)
    (htarget : Gamma.TargetsSection (sections.part j))
    (hshort : (sections.part j).length ≤ eps) :
    (Gamma.sourceArc.length : ℝ) ≤ lambda⁻¹ * (3 * (eps : ℝ) + c) :=
  Gamma.sourceArc_length_le_of_shortSection _ hcondition hlambda htarget
    (sections.quasiGeodesic j).1 hshort

end GroupApproximation.GGT.VanKampen.Embedded

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.Contiguity.sourceArc_quasi_lower
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.Contiguity.sourceArc_norm_le
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.Contiguity.targetArc_norm_le_of_shortSection
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.Contiguity.sourceArc_length_le_of_shortSection
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.Contiguity.sourceArc_length_le_of_boundarySection
