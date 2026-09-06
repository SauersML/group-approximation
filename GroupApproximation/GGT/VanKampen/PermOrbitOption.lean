import GroupApproximation.GGT.VanKampen.PermOrbitInsert

/-! # Adjoining a fixed point to a permutation adds one orbit -/

namespace GroupApproximation.GGT.VanKampen.PermOrbitOption

open Equiv
universe u
variable {D : Type u} [Finite D]

def orbitClass (p : Perm D) : Option D → Option (CombMap.Orbit p)
  | none => none
  | some d => some (Quotient.mk'' d)

noncomputable def representative (p : Perm D) : Option (CombMap.Orbit p) → Option D
  | none => none
  | some q => some q.out

noncomputable def orbitEquiv (p : Perm D) :
    CombMap.Orbit (Equiv.optionCongr p) ≃ Option (CombMap.Orbit p) :=
  OrbitClassifier.orbitEquiv (Equiv.optionCongr p) (orbitClass p) (representative p)
    (by
      intro d
      cases d with
      | none => rfl
      | some d =>
          exact congrArg some (Quotient.sound Perm.SameCycle.rfl.apply_left))
    (by
      intro q
      cases q with
      | none => rfl
      | some q => exact congrArg some q.out_eq)
    (by
      intro d
      cases d with
      | none => exact Perm.SameCycle.rfl
      | some d =>
          exact OrbitClassifier.sameCycle_map p (Equiv.optionCongr p) some (fun _ => rfl)
            (Quotient.exact (Quotient.out_eq (Quotient.mk'' d : CombMap.Orbit p))))

theorem orbit_card (p : Perm D) :
    Nat.card (CombMap.Orbit (Equiv.optionCongr p)) = Nat.card (CombMap.Orbit p) + 1 := by
  letI := Fintype.ofFinite (CombMap.Orbit p)
  rw [Nat.card_congr (orbitEquiv p)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_option]

end GroupApproximation.GGT.VanKampen.PermOrbitOption

#audit_axioms GroupApproximation.GGT.VanKampen.PermOrbitOption.orbitEquiv
#audit_axioms GroupApproximation.GGT.VanKampen.PermOrbitOption.orbit_card
