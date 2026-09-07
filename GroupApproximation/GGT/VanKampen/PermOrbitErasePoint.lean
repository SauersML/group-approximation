import GroupApproximation.GGT.VanKampen.PermOrbitSplit
import GroupApproximation.GGT.VanKampen.PermOrbitOption
import GroupApproximation.GGT.VanKampen.PermFirstReturnOrbits
import Mathlib.Logic.Equiv.Option

/-!
# Deleting a point from a permutation cycle

Deleting a point skips it in its old rotation cycle. Every non-singleton
cycle survives; a fixed-point cycle disappears. These exact counts are needed
when deleting the two darts of an edge, since a vertex may disappear as well.
-/

namespace GroupApproximation.GGT.VanKampen.PermOrbitErasePoint

open Equiv
universe u
variable {D : Type u} [DecidableEq D]

def isolate (p : Perm D) (a : D) : Perm D := Equiv.swap a (p a) * p

theorem isolate_fixed (p : Perm D) (a : D) : isolate p a a = a := by
  simp only [isolate, Perm.mul_apply, Equiv.swap_apply_right]

theorem isolate_ne_iff (p : Perm D) (a x : D) : isolate p a x ≠ a ↔ x ≠ a := by
  constructor
  · intro hn hx
    exact hn (hx ▸ isolate_fixed p a)
  · intro hx hq
    exact hx ((isolate p a).injective (hq.trans (isolate_fixed p a).symm))

/-- Erase the isolated point and retain every other point. -/
def erase (p : Perm D) (a : D) : Perm {x : D // x ≠ a} :=
  (isolate p a).subtypePerm (isolate_ne_iff p a)

theorem erase_val (p : Perm D) (a : D) (x : {x : D // x ≠ a}) :
    (erase p a x).1 = isolate p a x.1 := rfl

/-- This actual deletion is first return to the complement of the point. -/
theorem firstReturn (p : Perm D) (a : D) :
    PermFirstReturn.IsFirstReturn p (erase p a) (Function.Embedding.subtype _) := by
  intro x
  by_cases hx : p x.1 = a
  · refine ⟨2, by omega, ?_, ?_⟩
    · change (p ^ 2) x.1 = (erase p a x).1
      rw [erase_val, isolate, Perm.mul_apply, hx, Equiv.swap_apply_left,
        pow_two, Perm.mul_apply, hx]
    · intro k hk hk2 hret
      have hk1 : k = 1 := by omega
      obtain ⟨y, hy⟩ := hret
      have hy' : y.1 = (p ^ k) x.1 := hy
      exact y.property (by simpa only [hk1, pow_one, hx] using hy')
  · refine ⟨1, by omega, ?_, by intro k hk hk1; omega⟩
    change (p ^ 1) x.1 = (erase p a x).1
    rw [pow_one, erase_val, isolate, Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hx (p.injective.ne x.property)]

/-- Isolating the point splits the whole permutation into that fixed point
and its actual deletion. -/
theorem isolate_eq_permCongr (p : Perm D) (a : D) :
    isolate p a = (Equiv.optionSubtypeNe a).permCongr (Equiv.optionCongr (erase p a)) := by
  apply Equiv.ext
  intro d
  obtain ⟨x, rfl⟩ := (Equiv.optionSubtypeNe a).surjective d
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  cases x with
  | none => exact isolate_fixed p a
  | some x => rfl

/-- A permutation fixing the removed point acts on its complement. -/
def restrictFixed (t : Perm D) (a : D) (ha : t a = a) : Perm {x : D // x ≠ a} :=
  t.subtypePerm fun x => by
    constructor
    · intro hx heq
      exact hx (heq ▸ ha)
    · intro hx heq
      exact hx (t.injective (heq.trans ha.symm))

/-- Deletion commutes with right multiplication by a permutation fixing the
deleted point. This will identify the actual face rotation after edge deletion. -/
theorem erase_mul_of_fixed (p t : Perm D) (a : D) (ha : t a = a) :
    erase (p * t) a = erase p a * restrictFixed t a ha := by
  ext x
  change Equiv.swap a ((p * t) a) ((p * t) x.1) =
    Equiv.swap a (p a) (p (t x.1))
  simp only [Perm.mul_apply, ha]

variable [Fintype D]

theorem isolate_orbit_card (p : Perm D) (a : D) :
    Nat.card (CombMap.Orbit (isolate p a)) =
      Nat.card (CombMap.Orbit (erase p a)) + 1 := by
  rw [isolate_eq_permCongr, ← Nat.card_congr
    (orbitPermCongr (Equiv.optionSubtypeNe a) (Equiv.optionCongr (erase p a))),
    PermOrbitOption.orbit_card]

/-- Erasing a nonfixed point preserves the number of cycles. -/
theorem orbit_card_of_not_fixed (p : Perm D) (a : D) (ha : p a ≠ a) :
    Nat.card (CombMap.Orbit (erase p a)) = Nat.card (CombMap.Orbit p) := by
  have h := PermCycleCoordinates.orbit_card_swap_mul p a (p a) ha.symm
    Perm.SameCycle.rfl.apply_right
  have hi := isolate_orbit_card p a
  change Nat.card (CombMap.Orbit (isolate p a)) = Nat.card (CombMap.Orbit p) + 1 at h
  omega

/-- Erasing a fixed point removes its one-point cycle. -/
theorem orbit_card_of_fixed (p : Perm D) (a : D) (ha : p a = a) :
    Nat.card (CombMap.Orbit (erase p a)) + 1 = Nat.card (CombMap.Orbit p) := by
  have h := isolate_orbit_card p a
  have he : isolate p a = p := by
    ext x
    change Equiv.swap a (p a) (p x) = p x
    rw [ha, Equiv.swap_self]
    rfl
  rw [he] at h
  exact h.symm

/-- Equal images of the deleted point imply equal orbit-count losses. -/
theorem orbit_card_balance (p q : Perm D) (a : D) (ha : p a = q a) :
    Nat.card (CombMap.Orbit (erase p a)) + Nat.card (CombMap.Orbit q) =
      Nat.card (CombMap.Orbit (erase q a)) + Nat.card (CombMap.Orbit p) := by
  by_cases hp : p a = a
  · have hq : q a = a := ha.symm.trans hp
    have hcp := orbit_card_of_fixed p a hp
    have hcq := orbit_card_of_fixed q a hq
    omega
  · have hq : q a ≠ a := fun h => hp (ha.trans h)
    rw [orbit_card_of_not_fixed p a hp, orbit_card_of_not_fixed q a hq]
    omega

/-- Agreement on two deleted points gives the same total orbit loss. -/
theorem orbit_card_balance_twice (p q : Perm D) (a : D) (b : {x : D // x ≠ a})
    (ha : p a = q a) (hb : p b.1 = q b.1) :
    Nat.card (CombMap.Orbit (erase (erase p a) b)) + Nat.card (CombMap.Orbit q) =
      Nat.card (CombMap.Orbit (erase (erase q a) b)) + Nat.card (CombMap.Orbit p) := by
  have h₁ := orbit_card_balance p q a ha
  have hb' : erase p a b = erase q a b := by
    apply Subtype.ext
    change Equiv.swap a (p a) (p b.1) = Equiv.swap a (q a) (q b.1)
    rw [ha, hb]
  have h₂ := orbit_card_balance (erase p a) (erase q a) b hb'
  omega

end GroupApproximation.GGT.VanKampen.PermOrbitErasePoint

#audit_axioms GroupApproximation.GGT.VanKampen.PermOrbitErasePoint.firstReturn
#audit_axioms GroupApproximation.GGT.VanKampen.PermOrbitErasePoint.orbit_card_of_not_fixed
#audit_axioms GroupApproximation.GGT.VanKampen.PermOrbitErasePoint.orbit_card_of_fixed
#audit_axioms GroupApproximation.GGT.VanKampen.PermOrbitErasePoint.erase_mul_of_fixed
#audit_axioms GroupApproximation.GGT.VanKampen.PermOrbitErasePoint.orbit_card_balance
