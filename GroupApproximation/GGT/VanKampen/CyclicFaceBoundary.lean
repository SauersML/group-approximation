import GroupApproximation.GGT.VanKampen.SurgeryFaceKept
import GroupApproximation.GGT.VanKampen.FiniteCycleSplit

/-!
# Constructing a face boundary from an actual cyclic dart list

A nonempty duplicate-free list following face rotation and closing at its
start already enumerates exactly one face. Orbit completeness is proved from
the cyclic step, rather than supplied as a separate boundary oracle.
-/

namespace GroupApproximation.GGT.VanKampen.FaceBoundary

open Equiv
universe u

theorem cyclic_get_rotate {D : Type u} (p : Perm D) (l : List D) (hne : l ≠ [])
    (hchain : l.IsChain (fun d e => p d = e))
    (hclose : p (l.getLast hne) = l.head hne) (i : Fin l.length) :
    p (l.get i) = l.get (finRotate l.length i) := by
  have hpos : 0 < l.length := List.length_pos_iff.mpr hne
  have hi := i.isLt
  by_cases hlast : i.val + 1 = l.length
  · have hzero : finRotate l.length i = ⟨0, hpos⟩ := by
      apply Fin.ext
      rw [FiniteCycleSplit.rotate_val, if_pos hlast]
    rw [hzero]
    simpa only [List.getLast_eq_getElem, List.head_eq_getElem, List.get_eq_getElem,
      show l.length - 1 = i.val by omega] using hclose
  · have hnext : finRotate l.length i = ⟨i.val + 1, by omega⟩ := by
      apply Fin.ext
      rw [FiniteCycleSplit.rotate_val, if_neg hlast]
    rw [hnext]
    exact (List.isChain_iff_getElem.mp hchain) i.val (by omega)

theorem cyclic_mem_iff_sameCycle {D : Type u} [Finite D] (p : Perm D)
    (l : List D) (hne : l ≠ []) (hchain : l.IsChain (fun d e => p d = e))
    (hclose : p (l.getLast hne) = l.head hne) (d : D) :
    d ∈ l ↔ p.SameCycle (l.head hne) d := by
  have hpos : 0 < l.length := List.length_pos_iff.mpr hne
  constructor
  · intro hd
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hd
    have h := OrbitClassifier.sameCycle_map (finRotate l.length) p l.get
      (cyclic_get_rotate p l hne hchain hclose)
      (CactusShape.finRotate_sameCycle hpos ⟨0, hpos⟩ i)
    simpa only [List.get_eq_getElem, List.head_eq_getElem] using h
  · intro hd
    have hstep : ∀ x ∈ l, p x ∈ l := by
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hx
      rw [cyclic_get_rotate p l hne hchain hclose]
      exact List.get_mem _ _
    obtain ⟨n, hn⟩ := hd.exists_nat_pow_eq
    have hpow : ∀ n : ℕ, (p ^ n) (l.head hne) ∈ l := by
      intro n
      induction n with
      | zero => exact List.head_mem hne
      | succ n ih =>
          rw [pow_succ', Perm.mul_apply]
          exact hstep _ ih
    exact hn ▸ hpow n

/-- No additional orbit-completeness or degree assertion is needed. -/
noncomputable def ofCyclicList (M : CombMap.{u}) (l : List M.Dart) (hne : l ≠ [])
    (hnd : l.Nodup) (hchain : l.IsChain (fun d e => M.facePerm d = e))
    (hclose : M.facePerm (l.getLast hne) = l.head hne) :
    FaceBoundary M (M.faceOf (l.head hne)) := by
  have hmem : ∀ d, d ∈ l ↔ M.faceOf d = M.faceOf (l.head hne) := by
    intro d
    rw [cyclic_mem_iff_sameCycle M.facePerm l hne hchain hclose, M.faceOf_eq_iff]
    exact Perm.sameCycle_comm
  exact {
    darts := l
    nonempty := hne
    nodup := hnd
    mem_iff := hmem
    chain := hchain
    closes := hclose
    length_eq_degree := Surgery.MapCollapse.length_eq_faceDegree_of_nodup M _ l hnd hmem }

end GroupApproximation.GGT.VanKampen.FaceBoundary

#audit_axioms GroupApproximation.GGT.VanKampen.FaceBoundary.cyclic_get_rotate
#audit_axioms GroupApproximation.GGT.VanKampen.FaceBoundary.cyclic_mem_iff_sameCycle
#audit_axioms GroupApproximation.GGT.VanKampen.FaceBoundary.ofCyclicList
