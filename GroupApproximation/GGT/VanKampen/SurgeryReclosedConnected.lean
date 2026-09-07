import GroupApproximation.GGT.VanKampen.SurgeryReclosedFaces
import GroupApproximation.GGT.VanKampen.CombMapDual

/-!
# Reclosing along one boundary cycle preserves connectedness

All retained darts on the selected side belong to the new face. Collapse
those darts, and all deleted darts, to one representative for the purpose
of lifting ambient dual paths. Outside face rotations and retained edge
reversals lift to actual paths in the reclosed map. Ambient connectedness
therefore connects every pair of retained darts, before Euler preservation
or planarity of the result has been assumed.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv
universe v

theorem CombMap.eqvGen_of_sameCycle_facePerm (M : CombMap.{v})
    {x y : M.Dart} (hxy : M.facePerm.SameCycle x y) :
    Relation.EqvGen M.Adjacent x y := by
  obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
  have hstep (d : M.Dart) : Relation.EqvGen M.Adjacent d (M.facePerm d) :=
    .trans _ _ _ (.rel _ _ (Or.inl rfl)) (.rel _ _ (Or.inr rfl))
  have hpow : ∀ (m : ℕ) (d : M.Dart),
      Relation.EqvGen M.Adjacent d ((M.facePerm ^ m) d) := by
    intro m
    induction m with
    | zero => intro d; exact .refl _
    | succ m ih =>
        intro d
        rw [pow_succ, Perm.mul_apply]
        exact .trans _ _ _ (hstep d) (ih (M.facePerm d))
  simpa only [hn] using hpow n x

namespace Surgery.MapCollapse

/-- Connectedness of the reclosed map is a consequence of ambient
connectedness and the nonempty boundary cycle, not an additional oracle. -/
theorem reclosedMap_connected (M : CombMap.{v}) (faces : Finset M.Face)
    (boundary : BoundaryCycle M faces) (hM : M.IsConnected) :
    (reclosedMap M faces boundary).IsConnected := by
  classical
  let N := reclosedMap M faces boundary
  obtain ⟨b₀⟩ := nonempty_boundaryDart M faces boundary
  let b : N.Dart := ⟨b₀.val, fun h => b₀.property.2 h.2⟩
  let collapse : M.Dart → N.Dart := fun d =>
    if hd : M.faceOf d ∈ faces then b else ⟨d, fun h => hd h.1⟩
  have hboundary (d : N.Dart) (hd : M.faceOf d.val ∈ faces) :
      Relation.EqvGen N.Adjacent b d := by
    apply N.eqvGen_of_sameCycle_facePerm
    apply (N.faceOf_eq_iff b d).mp
    apply (reclosedFaceEquiv M faces boundary).injective
    rw [reclosedFaceEquiv_faceOf_mem M faces boundary b b₀.property.1,
      reclosedFaceEquiv_faceOf_mem M faces boundary d hd]
  have hcollapse (d : N.Dart) : Relation.EqvGen N.Adjacent (collapse d.val) d := by
    by_cases hd : M.faceOf d.val ∈ faces
    · simpa only [collapse, dif_pos hd] using hboundary d hd
    · have heq : collapse d.val = d := by
        simp only [collapse, dif_neg hd]
        exact Subtype.ext rfl
      rw [heq]
      exact .refl _
  have hface (d e : M.Dart) (heq : M.faceOf d = M.faceOf e) :
      Relation.EqvGen N.Adjacent (collapse d) (collapse e) := by
    by_cases hd : M.faceOf d ∈ faces
    · have he : M.faceOf e ∈ faces := heq ▸ hd
      simp only [collapse, dif_pos hd, dif_pos he]
      exact .refl _
    · have he : M.faceOf e ∉ faces := heq ▸ hd
      apply N.eqvGen_of_sameCycle_facePerm
      apply (N.faceOf_eq_iff _ _).mp
      apply (reclosedFaceEquiv M faces boundary).injective
      simp only [collapse, dif_neg hd, dif_neg he]
      rw [reclosedFaceEquiv_faceOf_notMem M faces boundary _ hd,
        reclosedFaceEquiv_faceOf_notMem M faces boundary _ he]
      exact congrArg Sum.inl (Subtype.ext heq)
  have halpha (d : M.Dart) :
      Relation.EqvGen N.Adjacent (collapse d) (collapse (M.alpha d)) := by
    by_cases hi : InternalDart M faces d
    · simp only [collapse, dif_pos hi.1, dif_pos hi.2]
      exact .refl _
    · let kd : N.Dart := ⟨d, hi⟩
      exact .trans _ _ _ (hcollapse kd)
        (.trans _ _ _ (.rel _ _ (Or.inl rfl)) (hcollapse (N.alpha kd)).symm)
  have hlift {d e : M.Dart} (h : Relation.EqvGen M.dual.Adjacent d e) :
      Relation.EqvGen N.Adjacent (collapse d) (collapse e) := by
    induction h with
    | rel d e h =>
        rcases h with h | h
        · rw [← h]
          exact halpha d
        · apply hface
          rw [← h]
          exact (M.faceOf_facePerm d).symm
    | refl d => exact .refl _
    | symm d e h ih => exact ih.symm
    | trans d e f h₁ h₂ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂
  intro d e
  exact .trans _ _ _ (hcollapse d).symm
    (.trans _ _ _ (hlift (M.dual_connected hM d.val e.val)) (hcollapse e))

/-- The historical disc-region interface can now be constructed from its
boundary and Euler equation; its connectedness field is proved. -/
def BoundaryCycle.toDiscRegion_of_euler (M : CombMap.{v}) (faces : Finset M.Face)
    (boundary : BoundaryCycle M faces) (hM : M.IsConnected)
    (heuler : (reclosedMap M faces boundary).eulerCharacteristic = M.eulerCharacteristic) :
    IsDiscRegion M faces where
  toBoundaryCycle := boundary
  reclosed_connected := reclosedMap_connected M faces boundary hM
  euler_preserved := heuler

end Surgery.MapCollapse
end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.eqvGen_of_sameCycle_facePerm
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.reclosedMap_connected
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.BoundaryCycle.toDiscRegion_of_euler
