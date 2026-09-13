import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSameCellSegments
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PolygonLists
import GroupApproximation.GGT.VanKampen.Estimating.Embedded
import Mathlib.Data.Nat.ModEq
import GroupApproximation.Meta.AxiomGuard

/-!
# Same-cell unbound darts: positions along a face boundary

The same-cell count scans a relator cell word from a base dart `x₀`, reading the darts
`x₀, f x₀, …, f^{n-1} x₀` for the face permutation `f`.  This module records the facts about
these positions that the count uses.
* `getElem_mod_pow`: the entry `k + t` of a face boundary, cyclically, is `f^t` of entry `k`.
* `pow_length`, `pow_inj`, `exists_pow_eq`, `mem_of_pow`: from any entry, the `n` face steps
  return to it, are distinct, and run over the whole boundary.
* `positionCount_eq_card`: counting positions is counting darts of the boundary.
* `getElem_darts`, `head?_eq_of_pred_not_mem`: the darts of a cyclic arc of a face boundary are
  face steps from its first dart, so a dart of the arc whose predecessor is off the arc is its
  first dart.

## Manuscript status

Infrastructure for `thm:hull` ("Hull's small cancellation theorem", through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe v

open scoped Classical

namespace OsinUnboundSameCellCycle

variable {M : CombMap.{v}} {F : M.Face}

/-- **A face boundary follows the face permutation cyclically.** -/
theorem getElem_mod_pow (B : FaceBoundary M F) {k : ℕ} (hk : k < B.darts.length) (t : ℕ) :
    B.darts[(k + t) % B.darts.length]'(Nat.mod_lt _ (by omega)) =
      (M.facePerm ^ t) B.darts[k] := by
  induction t with
  | zero => simp only [Nat.add_zero, Nat.mod_eq_of_lt hk, pow_zero, Equiv.Perm.one_apply]
  | succ t ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ← ih]
    have hstep := PolygonList.rel_getElem_mod B.nonempty B.chain B.closes
      ((k + t) % B.darts.length) (Nat.mod_lt _ (by omega))
    rw [hstep]
    simp only [Nat.mod_add_mod, Nat.add_assoc]

/-- **`n` face steps return.** -/
theorem pow_length (B : FaceBoundary M F) {k : ℕ} (hk : k < B.darts.length) :
    (M.facePerm ^ B.darts.length) B.darts[k] = B.darts[k] := by
  rw [← getElem_mod_pow B hk]
  simp only [Nat.add_mod_right, Nat.mod_eq_of_lt hk]

/-- **Fewer than `n` face steps are distinct.** -/
theorem pow_inj (B : FaceBoundary M F) {k : ℕ} (hk : k < B.darts.length) {a b : ℕ}
    (ha : a < B.darts.length) (hb : b < B.darts.length)
    (h : (M.facePerm ^ a) B.darts[k] = (M.facePerm ^ b) B.darts[k]) : a = b := by
  rw [← getElem_mod_pow B hk, ← getElem_mod_pow B hk] at h
  have hmod : k + a ≡ k + b [MOD B.darts.length] := (B.nodup.getElem_inj_iff).mp h
  exact (Nat.ModEq.add_left_cancel' k hmod).eq_of_lt_of_lt ha hb

/-- A face step from an entry stays on the boundary. -/
theorem mem_of_pow (B : FaceBoundary M F) {k : ℕ} (hk : k < B.darts.length) (j : ℕ) :
    (M.facePerm ^ j) B.darts[k] ∈ B.darts := by
  rw [← getElem_mod_pow B hk]
  exact List.getElem_mem _

/-- **Every dart of the boundary is fewer than `n` face steps from an entry.** -/
theorem exists_pow_eq (B : FaceBoundary M F) {k : ℕ} (hk : k < B.darts.length) {d : M.Dart}
    (hd : d ∈ B.darts) : ∃ j < B.darts.length, (M.facePerm ^ j) B.darts[k] = d := by
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hd
  refine ⟨(p + B.darts.length - k) % B.darts.length, Nat.mod_lt _ (by omega), ?_⟩
  rw [← getElem_mod_pow B hk]
  have e : k + (p + B.darts.length - k) = p + B.darts.length := by omega
  simp only [Nat.add_mod_mod, e, Nat.add_mod_right, Nat.mod_eq_of_lt hp]

/-- **Counting positions counts darts.**  The positions `j < n` whose dart `f^j x₀` satisfies `P`
number as many as the darts of the boundary that satisfy `P`. -/
theorem positionCount_eq_card (B : FaceBoundary M F) {k : ℕ} (hk : k < B.darts.length)
    (P : M.Dart → Prop) :
    positionCount (fun j => P ((M.facePerm ^ j) B.darts[k])) 0 B.darts.length =
      ((B.darts.toFinset.filter P).card : ℝ) := by
  simp only [positionCount, Finset.sum_boole]
  have himage : ((Finset.Ico 0 B.darts.length).filter
      fun j => P ((M.facePerm ^ j) B.darts[k])).image (fun j => (M.facePerm ^ j) B.darts[k]) =
        B.darts.toFinset.filter P := by
    ext d
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Ico, List.mem_toFinset]
    constructor
    · rintro ⟨j, ⟨-, hP⟩, rfl⟩
      exact ⟨mem_of_pow B hk j, hP⟩
    · rintro ⟨hd, hP⟩
      obtain ⟨j, hj, rfl⟩ := exists_pow_eq B hk hd
      exact ⟨j, ⟨⟨Nat.zero_le _, hj⟩, hP⟩, rfl⟩
  rw [← himage, Finset.card_image_of_injOn]
  intro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at ha hb
  exact pow_inj B hk ha.1.2 hb.1.2 hab

/-- **The darts of an arc are face steps from its first dart.** -/
theorem getElem_darts (B : FaceBoundary M F) {cycle : List M.Dart} (hcyc : cycle = B.darts)
    (A : Embedded.CyclicArc cycle) {t : ℕ} (ht : t < A.darts.length) :
    A.darts[t] = (M.facePerm ^ t)
      (B.darts[A.start.1 % B.darts.length]'(Nat.mod_lt _ (List.length_pos_iff.mpr B.nonempty))) := by
  subst hcyc
  rw [← getElem_mod_pow B (Nat.mod_lt _ (List.length_pos_iff.mpr B.nonempty))]
  simp only [Embedded.CyclicArc.darts, List.getElem_take, Embedded.CyclicArc.rotated_eq_rotate,
    List.getElem_rotate, Nat.mod_add_mod, Nat.add_comm t]

/-- **A dart of an arc whose predecessor is off the arc is its first dart.** -/
theorem head?_eq_of_pred_not_mem (B : FaceBoundary M F) {cycle : List M.Dart}
    (hcyc : cycle = B.darts) (A : Embedded.CyclicArc cycle) {d z : M.Dart} (hd : d ∈ A.darts)
    (hz : M.facePerm z = d) (hzA : z ∉ A.darts) : A.darts.head? = some d := by
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hd
  cases t with
  | zero =>
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem ht]
  | succ t =>
    exfalso
    have ht' : t < A.darts.length := by omega
    apply hzA
    have e : M.facePerm z = M.facePerm A.darts[t] := by
      rw [hz, getElem_darts B hcyc A ht, getElem_darts B hcyc A ht', pow_succ',
        Equiv.Perm.mul_apply]
    rw [M.facePerm.injective e]
    exact List.getElem_mem _

end OsinUnboundSameCellCycle

#audit_axioms GroupApproximation.GGT.VanKampen.OsinUnboundSameCellCycle.getElem_mod_pow
#audit_axioms GroupApproximation.GGT.VanKampen.OsinUnboundSameCellCycle.pow_length
#audit_axioms GroupApproximation.GGT.VanKampen.OsinUnboundSameCellCycle.pow_inj
#audit_axioms GroupApproximation.GGT.VanKampen.OsinUnboundSameCellCycle.mem_of_pow
#audit_axioms GroupApproximation.GGT.VanKampen.OsinUnboundSameCellCycle.exists_pow_eq
#audit_axioms GroupApproximation.GGT.VanKampen.OsinUnboundSameCellCycle.positionCount_eq_card
#audit_axioms GroupApproximation.GGT.VanKampen.OsinUnboundSameCellCycle.getElem_darts
#audit_axioms GroupApproximation.GGT.VanKampen.OsinUnboundSameCellCycle.head?_eq_of_pred_not_mem

end GroupApproximation.GGT.VanKampen
