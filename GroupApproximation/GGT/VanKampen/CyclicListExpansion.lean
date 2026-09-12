import GroupApproximation.GGT.VanKampen.CyclicFaceBoundary
import Mathlib.Data.List.Flatten

/-! # Expanding each entry of a cyclic walk into a nonempty walk -/

namespace GroupApproximation.GGT.VanKampen.CyclicListExpansion

open Equiv
universe u v
variable {A : Type u} {D : Type v}
variable (expand : A → List D) (hne : ∀ a, expand a ≠ [])

include hne in
theorem nonempty (l : List A) (hl : l ≠ []) : l.flatMap expand ≠ [] := by
  cases l with
  | nil => exact (hl rfl).elim
  | cons a l =>
      intro h
      rw [List.flatMap_cons, List.append_eq_nil_iff] at h
      exact hne a h.1

theorem head (l : List A) (hl : l ≠ []) :
    (l.flatMap expand).head (nonempty expand hne l hl) =
      (expand (l.head hl)).head (hne _) := by
  have hm : l.map expand ≠ [] := fun h => hl (List.map_eq_nil_iff.mp h)
  have hh : (l.map expand).head hm ≠ [] := by
    rw [List.head_map]
    exact hne _
  exact (List.head_head_eq_head_flatten hm hh).symm.trans (by simp only [List.head_map])

theorem getLast (l : List A) (hl : l ≠ []) :
    (l.flatMap expand).getLast (nonempty expand hne l hl) =
      (expand (l.getLast hl)).getLast (hne _) := by
  have hm : l.map expand ≠ [] := fun h => hl (List.map_eq_nil_iff.mp h)
  have hh : (l.map expand).getLast hm ≠ [] := by
    rw [List.getLast_map]
    exact hne _
  exact (List.getLast_getLast_eq_getLast_flatten hm hh).symm.trans (by simp only [List.getLast_map])

theorem chain (p : Perm A) (q : Perm D)
    (hblocks : ∀ a, (expand a).IsChain (fun d e => q d = e))
    (hjoin : ∀ a, q ((expand a).getLast (hne a)) = (expand (p a)).head (hne _))
    (l : List A) (hl : l.IsChain (fun a b => p a = b)) :
    (l.flatMap expand).IsChain (fun d e => q d = e) := by
  rw [List.flatMap]
  have hnil : [] ∉ l.map expand := by
    rw [List.mem_map]
    rintro ⟨a, _, ha⟩
    exact hne a ha
  apply (List.isChain_flatten hnil).mpr
  constructor
  · intro s hs
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hs
    exact hblocks a
  · rw [List.isChain_map]
    apply hl.imp
    intro a b hab d hd e he
    rw [List.getLast?_eq_some_getLast (hne a)] at hd
    rw [List.head?_eq_some_head (hne b)] at he
    obtain rfl := Option.mem_some_iff.mp hd
    obtain rfl := Option.mem_some_iff.mp he
    rw [hjoin, hab]

theorem closes (p : Perm A) (q : Perm D)
    (hjoin : ∀ a, q ((expand a).getLast (hne a)) = (expand (p a)).head (hne _))
    (l : List A) (hl : l ≠ []) (hclose : p (l.getLast hl) = l.head hl) :
    q ((l.flatMap expand).getLast (nonempty expand hne l hl)) =
      (l.flatMap expand).head (nonempty expand hne l hl) := by
  rw [getLast expand hne l hl, head expand hne l hl, hjoin, hclose]

end GroupApproximation.GGT.VanKampen.CyclicListExpansion

#audit_axioms GroupApproximation.GGT.VanKampen.CyclicListExpansion.chain
#audit_axioms GroupApproximation.GGT.VanKampen.CyclicListExpansion.closes
