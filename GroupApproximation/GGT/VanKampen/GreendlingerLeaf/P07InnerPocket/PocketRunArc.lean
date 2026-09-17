import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRunStep
import GroupApproximation.GGT.VanKampen.Estimating.Embedded
import GroupApproximation.GGT.VanKampen.FaceSetBoundaryRotation
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup
import Batteries.Data.List.Lemmas
import Batteries.Data.List.Perm
import GroupApproximation.Meta.AxiomGuard

/-!
# Runs follow their piece: face chains are cyclic arcs (lane `gl-p07-09`)

Let `B` be a face boundary with `n` darts.

* `facePerm_getElem`: `facePerm B[j] = B[(j+1) % n]`.  When `j + 1 < n` this is the chain.  When
  `j + 1 = n` it is `closes`, with `getLast = B[n-1]` and `head = B[0]`.
* `getElem_chain_eq`: let `u` be a `facePerm` chain with `u[0] = B[s]`.  Then `u[t] = B[(t+s) % n]`,
  by induction on `t`.  The step is `facePerm_getElem` together with
  `((t+s) % n + 1) % n = (t+1+s) % n`.
* `exists_cyclicArc_of_isChain`: a duplicate-free `facePerm` chain `u` of darts of `B` is the dart
  list of an arc.  The arc starts at the index `s` of `u[0]` and has length `u.length`, which is at
  most `n` because `u` is a duplicate-free sublist-up-to-permutation of `B`.  Compare entries with
  `getElem_rotate`.
* `getElem_last_of_facePerm_not_mem`, `eq_of_facePerm_not_mem`: the darts of an arc form a chain
  (a prefix of a rotation of the closed chain `B`).  So a dart of the arc whose `facePerm` leaves the
  arc sits at the last index, and there is at most one such dart.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121) through Osin's Lemma 9.7 (the inner pocket); certifies no
printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

open Embedded SimpleClosedWalkSides

universe u w v

namespace PocketRun

/-- The dart list of an explicit arc. -/
theorem darts_mk {α : Type*} (cyc : List α) (s : ℕ) (hs : s < cyc.length + 1) (l : ℕ)
    (hl : l ≤ cyc.length) :
    (CyclicArc.mk ⟨s, hs⟩ l hl : CyclicArc cyc).darts = (cyc.rotate s).take l :=
  congrArg (List.take l) (CyclicArc.rotated_eq_rotate (CyclicArc.mk ⟨s, hs⟩ l hl))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRun.darts_mk

section Boundary

variable {M : CombMap.{v}} {f : M.Face}

/-- **The face successor inside a boundary list**, cyclically indexed. -/
theorem facePerm_getElem (B : FaceBoundary M f) (j : ℕ) (hj : j < B.darts.length) :
    M.facePerm B.darts[j] = B.darts[(j + 1) % B.darts.length]'(Nat.mod_lt _ (by omega)) := by
  by_cases hlt : j + 1 < B.darts.length
  · have hstep : M.facePerm B.darts[j] = B.darts[j + 1] :=
      List.isChain_iff_getElem.mp B.chain j hlt
    exact hstep.trans (getElem_idx_congr B.darts (Nat.mod_eq_of_lt hlt).symm hlt _)
  · have hlast : j + 1 = B.darts.length := by omega
    have hmod : 0 = (j + 1) % B.darts.length := by rw [hlast, Nat.mod_self]
    have hc := B.closes
    rw [List.getLast_eq_getElem, List.head_eq_getElem] at hc
    exact (congrArg M.facePerm (getElem_idx_congr B.darts (i := j) (j := B.darts.length - 1)
      (by omega) hj (by omega))).trans
      (hc.trans (getElem_idx_congr B.darts hmod (by omega) (Nat.mod_lt _ (by omega))))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRun.facePerm_getElem

/-- The darts of an arc of a face boundary follow the face permutation. -/
theorem arcDarts_isChain (B : FaceBoundary M f) (A : CyclicArc B.darts) :
    A.darts.IsChain fun d e => M.facePerm d = e := by
  rw [CyclicArc.darts, CyclicArc.rotated_eq_rotate]
  exact (isChain_rotate_of_isChain_closes B.nonempty B.chain B.closes _).take _

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRun.arcDarts_isChain

/-- **A face chain starting at `B[s]` reads `B` from `s` on.** -/
theorem getElem_chain_eq (B : FaceBoundary M f) (u : List M.Dart)
    (hchain : u.IsChain fun d e => M.facePerm d = e) (s : ℕ) (hs : s < B.darts.length)
    (h0 : ∀ h : 0 < u.length, u[0] = B.darts[s]) (t : ℕ) (ht : t < u.length) :
    u[t] = B.darts[(t + s) % B.darts.length]'(Nat.mod_lt _ (by omega)) := by
  induction t with
  | zero =>
    exact (h0 ht).trans
      (getElem_idx_congr B.darts (by rw [Nat.zero_add, Nat.mod_eq_of_lt hs]) hs _)
  | succ t ih =>
    have hstep : M.facePerm u[t] = u[t + 1] := List.isChain_iff_getElem.mp hchain t ht
    have ht' : t < u.length := by omega
    exact hstep.symm.trans ((congrArg M.facePerm (ih ht')).trans
      ((facePerm_getElem B _ (Nat.mod_lt _ (by omega))).trans
        (getElem_idx_congr B.darts (by rw [Nat.mod_add_mod, Nat.add_right_comm t s 1]) _ _)))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRun.getElem_chain_eq

/-- **A duplicate-free face chain of boundary darts is an arc.** -/
theorem exists_cyclicArc_of_isChain (B : FaceBoundary M f) (u : List M.Dart) (hnd : u.Nodup)
    (hsub : ∀ x ∈ u, x ∈ B.darts) (hchain : u.IsChain fun d e => M.facePerm d = e) :
    ∃ A : CyclicArc B.darts, A.darts = u := by
  by_cases hu : u = []
  · subst hu
    exact ⟨⟨0, 0, Nat.zero_le _⟩, List.take_zero⟩
  · have hpos : 0 < u.length := List.length_pos_iff.mpr hu
    obtain ⟨s, hs, hsa⟩ := List.getElem_of_mem (hsub _ (List.getElem_mem hpos))
    have hle : u.length ≤ B.darts.length :=
      (List.subperm_of_subset hnd (fun hx => hsub _ hx)).length_le
    have hs1 : s < B.darts.length + 1 := by omega
    refine ⟨CyclicArc.mk ⟨s, hs1⟩ u.length hle, ?_⟩
    rw [darts_mk]
    refine List.ext_getElem (by rw [List.length_take, List.length_rotate]; omega) ?_
    intro i _ h₂
    rw [List.getElem_take, List.getElem_rotate]
    exact (getElem_chain_eq B u hchain s hs (fun _ => hsa.symm) i h₂).symm

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRun.exists_cyclicArc_of_isChain

/-- **Only the last dart of an arc can leave it.** -/
theorem getElem_last_of_facePerm_not_mem (B : FaceBoundary M f) (A : CyclicArc B.darts) (i : ℕ)
    (hi : i < A.darts.length) (hf : M.facePerm A.darts[i] ∉ A.darts) :
    i + 1 = A.darts.length := by
  by_contra hne
  have hlt : i + 1 < A.darts.length := by omega
  have hstep : M.facePerm A.darts[i] = A.darts[i + 1] :=
    List.isChain_iff_getElem.mp (arcDarts_isChain B A) i hlt
  exact hf (by rw [hstep]; exact List.getElem_mem hlt)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRun.getElem_last_of_facePerm_not_mem

/-- **At most one dart of an arc leaves it.** -/
theorem eq_of_facePerm_not_mem (B : FaceBoundary M f) (A : CyclicArc B.darts) {x y : M.Dart}
    (hx : x ∈ A.darts) (hy : y ∈ A.darts) (hfx : M.facePerm x ∉ A.darts)
    (hfy : M.facePerm y ∉ A.darts) : x = y := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
  have hi1 := getElem_last_of_facePerm_not_mem B A i hi hfx
  have hj1 := getElem_last_of_facePerm_not_mem B A j hj hfy
  exact getElem_idx_congr _ (by omega) hi hj

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRun.eq_of_facePerm_not_mem

end Boundary

end PocketRun

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
