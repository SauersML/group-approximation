import GroupApproximation.GGT.VanKampen.CombMapEdgeDeletionEuler
import GroupApproximation.GGT.VanKampen.PermOrbitJoinReach
import GroupApproximation.GGT.VanKampen.SurgeryReclosedConnected

/-!
# Deleting an edge between different faces preserves connectedness

The two old face cycles join. Retained darts in those cycles therefore lie
on one new face, providing a detour around the removed edge. Ambient dual
paths lift through this actual face and every other retained face. Neither
connectedness nor planarity of the deleted map is supplied as an input.
-/

namespace GroupApproximation.GGT.VanKampen.EdgeDeletion

open Equiv PermOrbitErasePoint
universe u
variable (M : CombMap.{u}) (a : M.Dart)

def ofValue (x : M.Dart) (hx : x ≠ a) (hb : x ≠ M.alpha a) : Dart M a :=
  ⟨⟨x, hx⟩, fun h => hb (congrArg Subtype.val h)⟩

theorem value_injective : Function.Injective (value M a) := by
  intro d e h
  exact Subtype.ext (Subtype.ext h)

variable [DecidableEq M.Dart]

abbrev joinedFacePerm : Perm M.Dart := M.sigma * unpair M a

theorem joinedFacePerm_eq : joinedFacePerm M a = M.facePerm * Equiv.swap a (M.alpha a) :=
  (mul_assoc _ _ _).symm

theorem joinedFacePerm_apply : joinedFacePerm M a a = M.sigma a := by
  rw [joinedFacePerm, Perm.mul_apply, unpair_fixed]

theorem joinedFacePerm_apply_reverse : joinedFacePerm M a (M.alpha a) = M.sigma (M.alpha a) := by
  rw [joinedFacePerm, Perm.mul_apply, unpair_fixed_reverse]

theorem joinedFacePerm_sameCycle (hface : M.faceOf a ≠ M.faceOf (M.alpha a)) :
    (joinedFacePerm M a).SameCycle a (M.alpha a) := by
  rw [joinedFacePerm_eq]
  exact PermCycleCoordinates.sameCycle_mul_swap_of_not_sameCycle M.facePerm a (M.alpha a)
    (fun h => hface ((M.faceOf_eq_iff _ _).mpr h))

theorem joinedFacePerm_of_sameCycle (hface : M.faceOf a ≠ M.faceOf (M.alpha a))
    {d e : M.Dart} (h : M.facePerm.SameCycle d e) :
    (joinedFacePerm M a).SameCycle d e := by
  have hab := joinedFacePerm_sameCycle M a hface
  rw [joinedFacePerm_eq] at hab ⊢
  exact PermCycleCoordinates.sameCycle_mul_swap_of_sameCycle _ _ _ hab h

theorem faceSameCycle_iff (d e : Dart M a) :
    (toCombMap M a).facePerm.SameCycle d e ↔
      (joinedFacePerm M a).SameCycle (value M a d) (value M a e) := by
  rw [facePerm_eq]
  exact (PermFirstReturn.sameCycle_iff _ _ _
    (firstReturn (erase (joinedFacePerm M a) a) (reverseDart M a)) d e).trans
      (PermFirstReturn.sameCycle_iff _ _ _ (firstReturn (joinedFacePerm M a) a) d.1 e.1)

/-- The joined face has a retained dart unless the edge was the whole
connected map. A dart of the actual remainder excludes that exception. -/
theorem exists_retained_joined_face (hM : M.IsConnected) (d : Dart M a)
    (hface : M.faceOf a ≠ M.faceOf (M.alpha a)) :
    ∃ c : Dart M a, (joinedFacePerm M a).SameCycle a (value M a c) := by
  obtain ⟨ha, hb⟩ := sigma_ne_of_neFace M a hface
  by_cases hsa : M.sigma a = M.alpha a
  · have hsb : M.sigma (M.alpha a) ≠ a := by
      intro hsb
      rcases M.dart_eq_or_alpha_of_swapped_endpoints hM a hsa hsb (value M a d) with h | h
      · exact value_ne M a d h
      · exact value_ne_reverse M a d h
    refine ⟨ofValue M a (M.sigma (M.alpha a)) hsb hb, ?_⟩
    have h := (joinedFacePerm_sameCycle M a hface).apply_right
    simpa only [joinedFacePerm_apply_reverse, value, ofValue] using h
  · refine ⟨ofValue M a (M.sigma a) ha hsa, ?_⟩
    have h : (joinedFacePerm M a).SameCycle a (joinedFacePerm M a a) :=
      Perm.SameCycle.rfl.apply_right
    simpa only [joinedFacePerm_apply, value, ofValue] using h

/-- Ambient connectedness implies connectedness after removing an edge with
different face sides. The empty remainder is covered by the same statement. -/
theorem connected_of_neFace (hM : M.IsConnected)
    (hface : M.faceOf a ≠ M.faceOf (M.alpha a)) : (toCombMap M a).IsConnected := by
  classical
  intro d e
  let N := toCombMap M a
  let q := joinedFacePerm M a
  obtain ⟨c, hc⟩ := exists_retained_joined_face M a hM d hface
  have hab : q.SameCycle a (M.alpha a) := joinedFacePerm_sameCycle M a hface
  let collapse : M.Dart → N.Dart := fun x =>
    if hx : q.SameCycle a x then c else
      ofValue M a x (fun h => hx (h.symm.sameCycle q))
        (fun h => hx (h ▸ hab))
  have hboundary (x : N.Dart) (hx : q.SameCycle a (value M a x)) :
      Relation.EqvGen N.Adjacent c x := by
    apply N.eqvGen_of_sameCycle_facePerm
    exact (faceSameCycle_iff M a c x).mpr (hc.symm.trans hx)
  have hcollapse (x : N.Dart) :
      Relation.EqvGen N.Adjacent (collapse (value M a x)) x := by
    by_cases hx : q.SameCycle a (value M a x)
    · simpa only [collapse, dif_pos hx] using hboundary x hx
    · have heq : collapse (value M a x) = x := by
        simp only [collapse, dif_neg hx]
        exact value_injective M a rfl
      rw [heq]
      exact .refl _
  have hfaceLift (x y : M.Dart) (hxy : M.facePerm.SameCycle x y) :
      Relation.EqvGen N.Adjacent (collapse x) (collapse y) := by
    have hq : q.SameCycle x y := joinedFacePerm_of_sameCycle M a hface hxy
    by_cases hx : q.SameCycle a x
    · have hy := hx.trans hq
      simp only [collapse, dif_pos hx, dif_pos hy]
      exact .refl _
    · have hy : ¬ q.SameCycle a y := fun hy => hx (hy.trans hq.symm)
      apply N.eqvGen_of_sameCycle_facePerm
      apply (faceSameCycle_iff M a _ _).mpr
      simpa only [collapse, dif_neg hx, dif_neg hy, value, ofValue] using hq
  have halpha (x : M.Dart) :
      Relation.EqvGen N.Adjacent (collapse x) (collapse (M.alpha x)) := by
    by_cases hx : x = a
    · subst x
      simp only [collapse, dif_pos (Perm.SameCycle.rfl : q.SameCycle a a), dif_pos hab]
      exact .refl _
    · by_cases hb : x = M.alpha a
      · subst x
        rw [M.alpha_involutive]
        simp only [collapse, dif_pos (Perm.SameCycle.rfl : q.SameCycle a a), dif_pos hab]
        exact .refl _
      · let x' : N.Dart := ofValue M a x hx hb
        have hy : value M a (N.alpha x') = M.alpha x := alpha_val M a x'
        have hpath := Relation.EqvGen.trans _ _ _ (hcollapse x')
          (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ (Or.inl rfl))
            (hcollapse (N.alpha x')).symm)
        change Relation.EqvGen N.Adjacent (collapse x)
          (collapse (value M a (N.alpha x'))) at hpath
        rw [hy] at hpath
        exact hpath
  have hlift {x y : M.Dart} (h : Relation.EqvGen M.dual.Adjacent x y) :
      Relation.EqvGen N.Adjacent (collapse x) (collapse y) := by
    induction h with
    | rel x y h =>
        rcases h with h | h
        · rw [← h]
          exact halpha x
        · rw [← h]
          exact hfaceLift x (M.facePerm x) Perm.SameCycle.rfl.apply_right
    | refl x => exact .refl _
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂
  exact .trans _ _ _ (hcollapse d).symm
    (.trans _ _ _ (hlift (M.dual_connected hM (value M a d) (value M a e))) (hcollapse e))

/-- The actual operation preserves planarity when an edge separates two
faces and at least one dart remains. -/
theorem planar_of_neFace (hM : M.IsPlanar) (d : Dart M a)
    (hface : M.faceOf a ≠ M.faceOf (M.alpha a)) : (toCombMap M a).IsPlanar :=
  ⟨connected_of_neFace M a hM.1 hface, (euler_eq_of_neFace M a hM.1 d hface).trans hM.2⟩

end GroupApproximation.GGT.VanKampen.EdgeDeletion

#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.exists_retained_joined_face
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.connected_of_neFace
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.planar_of_neFace
