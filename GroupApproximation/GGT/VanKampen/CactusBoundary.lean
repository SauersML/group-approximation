import GroupApproximation.GGT.VanKampen.CactusTopology
import GroupApproximation.GGT.VanKampen.DiscDiagram
import Mathlib.Data.List.NodupEquivFin
import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-!
# Ordered face boundaries for finite permutation maps

Mathlib's permutation cycle list omits fixed points.  A face of degree one
must still have a one-dart boundary, so this file adds a singleton fixed-point
branch.  The resulting list is nonempty, has no duplicates, follows face
rotation, closes cyclically, and enumerates exactly one face orbit.  Its
length is identified with the orbit fibre cardinality by `List.Nodup.getEquiv`.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

open Equiv

/-- The nonempty ordered orbit list of a dart. -/
def closedOrbitList {D : Type*} [Fintype D] [DecidableEq D]
    (p : Perm D) (d : D) : List D :=
  if p d = d then [d] else p.toList d

namespace closedOrbitList

theorem nonempty {D : Type*} [Fintype D] [DecidableEq D]
    (p : Perm D) (d : D) : closedOrbitList p d ≠ [] := by
  by_cases hd : p d = d
  · simp [closedOrbitList, hd]
  · rw [closedOrbitList, if_neg hd]
    exact (Equiv.Perm.toList_eq_nil_iff.not.mpr
      (by simpa [Equiv.Perm.mem_support] using hd))

theorem nodup {D : Type*} [Fintype D] [DecidableEq D]
    (p : Perm D) (d : D) : (closedOrbitList p d).Nodup := by
  by_cases hd : p d = d
  · simp [closedOrbitList, hd]
  · rw [closedOrbitList, if_neg hd]
    exact Equiv.Perm.nodup_toList p d

/-- Membership in the closed orbit list is exactly the same-cycle relation. -/
theorem mem_iff_sameCycle {D : Type*} [Fintype D] [DecidableEq D]
    (p : Perm D) (d e : D) :
    e ∈ closedOrbitList p d ↔ p.SameCycle d e := by
  by_cases hd : p d = d
  · rw [closedOrbitList, if_pos hd, List.mem_singleton]
    constructor
    · intro he
      exact he.symm.sameCycle p
    · intro hcycle
      exact (hcycle.eq_of_left hd).symm
  · rw [closedOrbitList, if_neg hd, Equiv.Perm.mem_toList_iff]
    simp [Equiv.Perm.mem_support, hd]

/-- Consecutive entries follow the permutation. -/
theorem chain {D : Type*} [Fintype D] [DecidableEq D]
    (p : Perm D) (d : D) :
    (closedOrbitList p d).IsChain fun x y ↦ p x = y := by
  by_cases hd : p d = d
  · simp [closedOrbitList, hd]
  · rw [closedOrbitList, if_neg hd, List.isChain_iff_getElem]
    intro n hn
    rw [Equiv.Perm.getElem_toList, Equiv.Perm.getElem_toList]
    rw [← Perm.mul_apply, ← pow_succ']

/-- The final entry rotates to the first entry. -/
theorem closes {D : Type*} [Fintype D] [DecidableEq D]
    (p : Perm D) (d : D) :
    p ((closedOrbitList p d).getLast (nonempty p d)) =
      (closedOrbitList p d).head (nonempty p d) := by
  by_cases hd : p d = d
  · simp [closedOrbitList, hd]
  · let l := p.toList d
    have hl : l ≠ [] := Equiv.Perm.toList_eq_nil_iff.not.mpr
      (by simpa [Equiv.Perm.mem_support] using hd)
    have hn : l.Nodup := Equiv.Perm.nodup_toList p d
    have hmem : l.getLast hl ∈ l := List.getLast_mem hl
    have hnext := Equiv.Perm.next_toList_eq_apply p d (l.getLast hl) hmem
    have hlast := List.next_getLast_eq_head l hl hn
    simp only [closedOrbitList, if_neg hd]
    exact hnext.symm.trans hlast

/-- The closed orbit list has the cardinality of the orbit fibre. -/
theorem length_eq_orbitDegree {D : Type*} [Fintype D] [DecidableEq D]
    (p : Perm D) (d : D) :
    (closedOrbitList p d).length =
      CombMap.orbitDegree p (Quotient.mk'' d) := by
  let l := closedOrbitList p d
  have hn : l.Nodup := nodup p d
  let e₁ : Fin l.length ≃ {x : D // x ∈ l} := hn.getEquiv l
  have hpred : (fun x : D ↦ x ∈ l) =
      (fun x : D ↦ (Quotient.mk'' x : CombMap.Orbit p) = Quotient.mk'' d) := by
    funext x
    apply propext
    rw [mem_iff_sameCycle]
    constructor
    · intro h
      exact Quotient.sound h.symm
    · intro h
      exact (Quotient.eq''.mp h).symm
  let e₂ : {x : D // x ∈ l} ≃
      {x : D // (Quotient.mk'' x : CombMap.Orbit p) = Quotient.mk'' d} :=
    Equiv.subtypeEquivProp hpred
  change l.length = Nat.card
    {x : D // (Quotient.mk'' x : CombMap.Orbit p) = Quotient.mk'' d}
  rw [← Nat.card_fin l.length]
  exact Nat.card_congr (e₁.trans e₂)

end closedOrbitList

namespace FaceBoundary

/-- The canonical ordered boundary based at a chosen dart. -/
noncomputable def based (M : CombMap.{0}) (d : M.Dart) :
    FaceBoundary M (M.faceOf d) := by
  classical
  exact
    { darts := closedOrbitList M.facePerm d
      nonempty := closedOrbitList.nonempty M.facePerm d
      nodup := closedOrbitList.nodup M.facePerm d
      mem_iff := fun e ↦ by
        rw [closedOrbitList.mem_iff_sameCycle, M.faceOf_eq_iff]
        exact Equiv.Perm.sameCycle_comm
      chain := closedOrbitList.chain M.facePerm d
      closes := closedOrbitList.closes M.facePerm d
      length_eq_degree := closedOrbitList.length_eq_orbitDegree M.facePerm d }

end FaceBoundary

end VanKampen
end GGT
end GroupApproximation
