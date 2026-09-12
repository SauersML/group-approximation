import GroupApproximation.GGT.VanKampen.CombMapEdgeFaces
import GroupApproximation.GGT.VanKampen.SurgeryFaceKept

/-!
# The faces untouched by corner-edge insertion

Insertion into one face preserves the actual face cycles outside that face.
The old-face classifier proves that no fresh dart enters an untouched face;
the face-rotation formula transports all of its old darts. Thus its ordered
boundary, and consequently every word read on it, can be retained literally.
-/

namespace GroupApproximation.GGT.VanKampen.EdgeInsertion

open Equiv PermOrbitInsert
universe u

theorem embed_injective (M : CombMap.{u}) : Function.Injective (embed M) := by
  intro d e h
  exact Option.some.inj (Option.some.inj h)

/-- Both new darts belong to pieces of the chosen old face. -/
def oldFaceClass (M : CombMap.{u}) (a : M.Dart) : Dart M → M.Face
  | none => M.faceOf a
  | some none => M.faceOf a
  | some (some d) => M.faceOf d

theorem oldFaceClass_invariant (M : CombMap.{u}) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (d : Dart M) :
    oldFaceClass M a ((toCombMap M a b).facePerm d) = oldFaceClass M a d := by
  classical
  rcases d with _ | (_ | d)
  · change oldFaceClass M a (insertBefore (insertBefore M.sigma a) (some b) (some none)) = _
    by_cases hab : a = b
    · simp [insertBefore_some, hab, oldFaceClass]
    · simp [insertBefore_some, hab, oldFaceClass]
  · change oldFaceClass M a (insertBefore (insertBefore M.sigma a) (some b) none) = _
    rw [insertBefore_none]
    exact hface.symm
  · change oldFaceClass M a
      (insertBefore (insertBefore M.sigma a) (some b) (some (some (M.alpha d)))) = M.faceOf d
    by_cases ha : M.sigma (M.alpha d) = a
    · simp only [insertBefore_some, if_pos ha, reduceCtorEq, if_false]
      change M.faceOf a = M.faceOf d
      exact (congrArg M.faceOf ha.symm).trans (M.faceOf_facePerm d)
    · by_cases hb : M.sigma (M.alpha d) = b
      · simp only [insertBefore_some, if_neg ha, Option.some.injEq, if_pos hb]
        change M.faceOf a = M.faceOf d
        exact hface.trans ((congrArg M.faceOf hb.symm).trans (M.faceOf_facePerm d))
      · simp only [insertBefore_some, if_neg ha, Option.some.injEq, if_neg hb]
        exact M.faceOf_facePerm d

/-- Sending each new face to the old face in which it lies. -/
noncomputable def faceMap (M : CombMap.{u}) (a b : M.Dart) (hface : M.faceOf a = M.faceOf b) :
    (toCombMap M a b).Face → M.Face :=
  Quotient.lift (oldFaceClass M a) (fun _ _ h =>
    OrbitClassifier.eq_of_sameCycle (toCombMap M a b).facePerm (oldFaceClass M a)
      (oldFaceClass_invariant M a b hface) h)

@[simp] theorem faceMap_faceOf (M : CombMap.{u}) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (d : Dart M) :
    faceMap M a b hface ((toCombMap M a b).faceOf d) = oldFaceClass M a d := rfl

/-- Rotation on an untouched face retains each old step exactly. -/
theorem facePerm_embed_of_ne (M : CombMap.{u}) (a b d : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hd : M.faceOf d ≠ M.faceOf a) :
    (toCombMap M a b).facePerm (embed M d) = embed M (M.facePerm d) := by
  classical
  have ha : M.sigma (M.alpha d) ≠ a := by
    intro h
    exact hd ((M.faceOf_facePerm d).symm.trans (congrArg M.faceOf h))
  have hb : M.sigma (M.alpha d) ≠ b := by
    intro h
    exact hd (((M.faceOf_facePerm d).symm.trans (congrArg M.faceOf h)).trans hface.symm)
  change insertBefore (insertBefore M.sigma a) (some b) (some (some (M.alpha d))) =
    some (some (M.sigma (M.alpha d)))
  simp only [insertBefore_some, if_neg ha, Option.some.injEq, if_neg hb]

/-- A whole old face cycle lifts when it is outside the insertion face. -/
theorem sameCycle_embed_of_ne (M : CombMap.{u}) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) {d e : M.Dart}
    (hd : M.faceOf d ≠ M.faceOf a) (hde : M.facePerm.SameCycle d e) :
    (toCombMap M a b).facePerm.SameCycle (embed M d) (embed M e) := by
  obtain ⟨n, hn⟩ := hde.exists_nat_pow_eq
  have hpow : ∀ (m : ℕ) (x : M.Dart), M.faceOf x ≠ M.faceOf a →
      (toCombMap M a b).facePerm.SameCycle (embed M x) (embed M ((M.facePerm ^ m) x)) := by
    intro m
    induction m with
    | zero => intro x hx; exact Perm.SameCycle.rfl
    | succ m ih =>
        intro x hx
        rw [pow_succ, Perm.mul_apply]
        have hstep : (toCombMap M a b).facePerm.SameCycle
            (embed M x) (embed M (M.facePerm x)) := by
          rw [← facePerm_embed_of_ne M a b x hface hx]
          exact Perm.SameCycle.rfl.apply_right
        exact hstep.trans (ih (M.facePerm x) (by rwa [M.faceOf_facePerm]))
  simpa only [hn] using hpow n d hd

/-- The old face can be recovered from its untouched new cycle. -/
theorem faceOf_embed_eq_iff (M : CombMap.{u}) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (d e : M.Dart)
    (hd : M.faceOf d ≠ M.faceOf a) :
    (toCombMap M a b).faceOf (embed M d) = (toCombMap M a b).faceOf (embed M e) ↔
      M.faceOf d = M.faceOf e := by
  constructor
  · intro h
    exact congrArg (faceMap M a b hface) h
  · intro h
    exact Quotient.sound (sameCycle_embed_of_ne M a b hface hd ((M.faceOf_eq_iff d e).mp h))

end GroupApproximation.GGT.VanKampen.EdgeInsertion

#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.oldFaceClass_invariant
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.facePerm_embed_of_ne
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.faceOf_embed_eq_iff
