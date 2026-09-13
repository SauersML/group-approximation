import GroupApproximation.GGT.HullSCLemma51LetterPullbackCutLift
import GroupApproximation.GGT.HullSCLemma51EmbeddedBridge

/-!
# The certificate-cut move of the letter pullback

A lifted quotient-null word `w = p ++ [comp λ h⁻¹]` all of whose rotations are geodesic has a
certificate cut (`exists_geodesicCut_of_leastAreaCertificates`): a rotation
`before ++ arc ++ after` and a relator `ext ++ rem ∈ W` with a face `ext = L · arc · R` and
`|L| + |rem| + |R| < |arc|`.  Rotating further by `|before|` puts the arc first,
`arc ++ (after ++ before)`, and the same rotation is a rotated lift `x ++ comp λ h⁻¹ :: y`.
This is a cut lift (`CutLift`).  An outcome of every cut lift (`CutLiftOutcome`) gives the move
bound at radius `2 ε + n + L_W + 2` and count `2 ε + n + L_W + 3`, where `L_W` bounds the relator
lengths.
-/

namespace GroupApproximation
namespace HullSC

universe u v w

variable {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}

/-- **The move bound for words with every rotation geodesic**, from the outcome of cut lifts. -/
theorem letterStepBound_of_cutLiftOutcome (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))} {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsBoundedLemma44Input D W eps mu rho) (hmu : mu ≤ 1 / 1000)
    (hrho : 20 * (eps + 1) ≤ rho) (q : G →* Q) (hq : Function.Surjective q)
    (hker : q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hcert : ∀ (R : ℕ) (Z : RelativeLeastAreaDiagram D W R),
      Z.toRelativeReducedDiagram.HasQuasiGeodesicSpelling →
        Nonempty (RelativeDiagramCertificate D W eps mu Z.toRelativeReducedDiagram))
    (hout : CutLiftOutcome W D q hq) :
    LetterStepBound D W q hq (fun w => ∀ r : ℕ, IsRelGeodesic D (w.rotate r)) := by
  obtain ⟨LW, hLW⟩ := hsc.lengthBounded
  refine ⟨fun n => 2 * eps + n + LW + 2, fun n => 2 * eps + n + LW + 3, ?_⟩
  intro lam n h p hh hp hlen havoid hqp hne hP
  show PullbackOutcome D q hq lam (pullbackAtoms W D lam (2 * eps + n + LW + 2))
    (2 * eps + n + LW + 3) h n
  have hgeo : ∀ r : ℕ, IsRelGeodesic D ((p ++ [GGT.RelLetter.comp lam h⁻¹]).rotate r) := hP
  have hw : RelWord.IsAdmissible D (p ++ [GGT.RelLetter.comp lam h⁻¹]) := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hp a ha
    · rw [List.mem_singleton] at ha
      subst ha
      exact inv_mem hh
  have ev : (GGT.RelLetter.comp lam h⁻¹ : GGT.RelLetter G Lambda).val = h⁻¹ := rfl
  have hwval : GGT.RelLetter.listVal (p ++ [GGT.RelLetter.comp lam h⁻¹]) =
      GGT.RelLetter.listVal p * h⁻¹ := by
    rw [GGT.OsinComponents.listVal_append, RelWord.listVal_singleton, ev]
  have hqw : q (GGT.RelLetter.listVal (p ++ [GGT.RelLetter.comp lam h⁻¹])) = 1 := by
    rw [hwval, map_mul, hqp, map_inv, mul_inv_cancel]
  have hnew : GGT.RelLetter.listVal (p ++ [GGT.RelLetter.comp lam h⁻¹]) ≠ 1 := by
    rw [hwval]
    intro h1
    exact hne (mul_inv_eq_one.mp h1)
  obtain ⟨r, before, arc, after, L, R, ext, rem, hrot, hmem, hLadm, hLgeo, hLlen, hRadm, hRgeo,
      hRlen, harcgeo, hval, hshort⟩ :=
    exists_geodesicCut_of_leastAreaCertificates D hsc.toIsLemma44Input hmu hrho q hker hcert hw
      hqw hnew hgeo
  have hrot' : (p ++ [GGT.RelLetter.comp lam h⁻¹]).rotate (r + before.length) =
      arc ++ (after ++ before) := by
    rw [← List.rotate_rotate, hrot, List.append_assoc, List.rotate_append_length_eq,
      List.append_assoc]
  obtain ⟨x, y, c, hsplit, hlift⟩ :=
    exists_rotatedLift D q hq hh hp havoid hqp (r + before.length)
  have hwlen : p.length + 1 = before.length + arc.length + after.length := by
    have e := congrArg List.length hrot
    simp only [List.length_rotate, List.length_append, List.length_cons, List.length_nil] at e
    omega
  have hslen : x.length + y.length = p.length := by
    have e := congrArg List.length hsplit
    simp only [List.length_rotate, List.length_append, List.length_cons, List.length_nil] at e
    omega
  have harcadm : RelWord.IsAdmissible D arc := by
    intro a ha
    have hmemrot : a ∈ (p ++ [GGT.RelLetter.comp lam h⁻¹]).rotate r := by
      rw [hrot]
      exact List.mem_append_left _ (List.mem_append_right _ ha)
    exact hw a (List.mem_rotate.mp hmemrot)
  have hadm : RelWord.IsAdmissible D (ext ++ rem) := hsc.admissible _ hmem
  have hextlen : ext.length ≤ LW := by
    have e := hLW _ hmem
    simp only [List.length_append] at e
    omega
  have hcl : CutLift W D q hq lam h c L arc R ext rem (after ++ before) x y :=
    { lift := hlift
      mem := hh
      face :=
        { left_adm := hLadm
          left_geo := hLgeo
          arc_adm := harcadm
          arc_geo := harcgeo
          right_adm := hRadm
          right_geo := hRgeo
          ext_adm := fun a ha => hadm a (List.mem_append_left _ ha)
          ext_sub := ⟨ext ++ rem, hmem, fun a ha => List.mem_append_left _ ha⟩
          value := hval
          short := by omega }
      split := hrot'.symm.trans hsplit
      relator := hmem
      rem_adm := fun a ha => hadm a (List.mem_append_right _ ha)
      rem_null := by
        have e := map_listVal_eq_one_of_ker_eq_normalClosure q hker _ hmem
        rwa [GGT.OsinComponents.listVal_append] at e
      short := hshort }
  exact hout hcl (by omega) (by omega) (by omega) (by omega)

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.letterStepBound_of_cutLiftOutcome
