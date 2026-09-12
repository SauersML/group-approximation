import GroupApproximation.GGT.VanKampen.CombMapEdgeInsertion

/-!
# The face permutation after edge insertion

For distinct corners, edge insertion cuts the old face permutation by a
transposition and then inserts the two new darts into the resulting cycles.
For equal corners, one new dart is a monogon and the other is inserted into
the old face. These exact identities reduce the face count to permutation
orbit calculations; they do not assume the desired face-count conclusion.
-/

namespace GroupApproximation.GGT.VanKampen.EdgeInsertion

open Equiv PermOrbitInsert
universe u

theorem facePerm_eq_of_ne (M : CombMap.{u}) [DecidableEq M.Dart]
    (a b : M.Dart) (hab : a ≠ b) :
    (toCombMap M a b).facePerm =
      insertBefore (insertBefore (Equiv.swap a b * M.facePerm) b) (some a) := by
  classical
  ext d
  rcases d with _ | (_ | d)
  · change insertBefore (insertBefore M.sigma a) (some b) (some none) =
      insertBefore (insertBefore (Equiv.swap a b * M.facePerm) b) (some a) none
    simp only [insertBefore_some, insertBefore_none, Option.some.injEq, if_neg hab]
  · change insertBefore (insertBefore M.sigma a) (some b) none =
      insertBefore (insertBefore (Equiv.swap a b * M.facePerm) b) (some a) (some none)
    simp only [insertBefore_some, insertBefore_none, Option.some.injEq, if_neg hab.symm]
  · change insertBefore (insertBefore M.sigma a) (some b) (some (some (M.alpha d))) =
      insertBefore (insertBefore (Equiv.swap a b * M.facePerm) b) (some a) (some (some d))
    by_cases hfa : M.sigma (M.alpha d) = a
    · simp [insertBefore_some, Perm.mul_apply, CombMap.facePerm, hfa]
    · by_cases hfb : M.sigma (M.alpha d) = b
      · simp [insertBefore_some, Perm.mul_apply, CombMap.facePerm, hfb, hab.symm, hab]
      · simp [insertBefore_some, Perm.mul_apply, CombMap.facePerm, hfa, hfb,
          Equiv.swap_apply_def]

theorem facePerm_eq_of_eq (M : CombMap.{u}) (a : M.Dart) :
    (toCombMap M a a).facePerm = Equiv.optionCongr (insertBefore M.facePerm a) := by
  classical
  ext d
  rcases d with _ | (_ | d)
  · change insertBefore (insertBefore M.sigma a) (some a) (some none) = none
    simp [insertBefore_some]
  · change insertBefore (insertBefore M.sigma a) (some a) none = some (insertBefore M.facePerm a none)
    simp only [insertBefore_none]
  · change insertBefore (insertBefore M.sigma a) (some a) (some (some (M.alpha d))) =
      some (insertBefore M.facePerm a (some d))
    by_cases hfa : M.sigma (M.alpha d) = a
    · simp [insertBefore_some, CombMap.facePerm, Perm.mul_apply, hfa]
    · simp [insertBefore_some, CombMap.facePerm, Perm.mul_apply, hfa]

end GroupApproximation.GGT.VanKampen.EdgeInsertion

#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.facePerm_eq_of_ne
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.facePerm_eq_of_eq
