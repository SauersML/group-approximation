import GroupApproximation.GGT.VanKampen.CombMap

/-!
# Transporting permutation orbits

Two general facts about `CombMap.Orbit`, which is the quotient of a type by the
same-cycle relation of a permutation.  They are the first half of the
description of the faces of a reclosed map: its face permutation is an
equivalence conjugating a sum of two permutations, one of which is a single
cycle.

`orbitPermCongr` transports orbits along an equivalence of the underlying
types, and `orbitEquivPUnit` says a permutation whose points all lie in one
cycle has exactly one orbit.

Nothing here mentions maps, darts or faces.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

universe u

/-! ## Powers along a conjugation -/

/-- A power of a conjugated permutation is the conjugate of the power. -/
theorem permCongr_zpow {α β : Type u} (e : α ≃ β) (p : Equiv.Perm α) (i : ℤ)
    (x : α) : ((e.permCongr p) ^ i) (e x) = e ((p ^ i) x) := by
  have hpow : (e.permCongr p) ^ i = e.permCongr (p ^ i) :=
    (map_zpow (Equiv.permCongrHom e) p i).symm
  rw [hpow, Equiv.permCongr_apply, e.symm_apply_apply]

/-- Being in the same cycle is preserved and reflected by a conjugation. -/
theorem sameCycle_permCongr {α β : Type u} (e : α ≃ β) (p : Equiv.Perm α)
    (x y : α) :
    Equiv.Perm.SameCycle p x y ↔
      Equiv.Perm.SameCycle (e.permCongr p) (e x) (e y) := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [permCongr_zpow e p i x, hi]
  · rintro ⟨i, hi⟩
    refine ⟨i, e.injective ?_⟩
    rw [← permCongr_zpow e p i x, hi]

/-- Orbits transport along an equivalence of the underlying types. -/
noncomputable def orbitPermCongr {α β : Type u} (e : α ≃ β) (p : Equiv.Perm α) :
    CombMap.Orbit p ≃ CombMap.Orbit (e.permCongr p) :=
  Quotient.congr e (fun x y => sameCycle_permCongr e p x y)

/-! ## A single cycle has a single orbit -/

/-- A permutation whose points all lie in one cycle has exactly one orbit. -/
noncomputable def orbitEquivPUnit {α : Type u} [Nonempty α]
    (p : Equiv.Perm α) (h : ∀ x y : α, Equiv.Perm.SameCycle p x y) :
    CombMap.Orbit p ≃ PUnit.{u + 1} where
  toFun _ := PUnit.unit
  invFun _ := Quotient.mk'' (Classical.arbitrary α)
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    exact Quotient.sound (h (Classical.arbitrary α) x)
  right_inv := by
    intro u
    cases u
    rfl

end VanKampen
end GGT
end GroupApproximation
