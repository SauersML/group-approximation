import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2PosStabGen
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.Data.Set.Finite.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Stabilized normal generation of `K₂`: the base rank and the rank step, any ring

Lane `bh-met-72c`, helper module.  Everything here holds over an arbitrary unital ring `R`, with
no hypothesis beyond the displayed ones.  Write `T(n)` for the property

  `∃ s ⊆ K₂(n, R)` finite with `K₂(n+1, R) ≤ ⟪stab '' s⟫` (normal closure in `St_{n+1}(R)`),

which is the instance of `CharZeroK2PosStabGenStatement` at one rank.

* `czStabGen_base`: if `K₂(n+1, R)` is the normal closure (in `St_{n+1}(R)`) of a finite set and
  `K₂(n+1, R) ≤ stab K₂(n, R)`, then `T(n)`.  Every element of the finite normal generating set
  `t` lies in `K₂(n+1) ≤ stab K₂(n)`, so it has a preimage in `K₂(n)`; a finite choice of
  preimages `s` has `stab '' s = t` (`Set.exists_subset_image_finite_and`).  No centrality is used.
* `czStabGen_step`: `T(n)` and `K₂(n+2, R) ≤ stab K₂(n+1, R)` give `T(n+1)`, with the new set
  `stab '' s`.  Indeed `stab ⟪stab '' s⟫ ≤ ⟪stab '' (stab '' s)⟫`
  (`Subgroup.map_normalClosure_le`), and `stab '' s ⊆ K₂(n+1)`.
* `czStabGen_fng_of_T`, `czStabGen_surj_of_T`: conversely `T(n)` gives both inputs of the base
  step at rank `n` (finite normal generation of `K₂(n+1)` and surjective stability at `n`).  These
  use the padded centrality theorem, through `closure_stab_image_eq_K2` (lane `bh-met-47`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic

variable {R : Type*} [Ring R] {n : ℕ}

/-- **Base rank.**  Finite normal generation of `K₂(n+1, R)` in `St_{n+1}(R)` and surjective
stability `K₂(n+1, R) ≤ stab K₂(n, R)` give a finite `s ⊆ K₂(n, R)` whose stabilization normally
generates `K₂(n+1, R)`. -/
theorem czStabGen_base (hfn : (K2 (Fin (n + 1)) R).IsFinitelyNormallyGenerated)
    (hsurj : K2 (Fin (n + 1)) R ≤ (K2 (Fin n) R).map (stab n R)) :
    ∃ s : Set (St n R), s.Finite ∧ s ⊆ K2 (Fin n) R ∧
      K2 (Fin (n + 1)) R ≤ Subgroup.normalClosure (stab n R '' s) := by
  obtain ⟨t, htfin, ht⟩ := hfn
  have htsub : t ⊆ stab n R '' (K2 (Fin n) R : Set (St n R)) := by
    intro y hy
    have hyK : y ∈ K2 (Fin (n + 1)) R := by
      rw [← ht]
      exact Subgroup.subset_normalClosure hy
    obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.mp (hsurj hyK)
    exact ⟨k, hk, hky⟩
  obtain ⟨s, hsK, hsfin, hst⟩ :=
    (Set.exists_subset_image_finite_and (f := ⇑(stab n R))
      (s := (K2 (Fin n) R : Set (St n R))) (p := fun u ↦ u = t)).mp ⟨t, htsub, htfin, rfl⟩
  have hst' : stab n R '' s = t := hst
  exact ⟨s, hsfin, hsK, (ht.symm.trans (congrArg Subgroup.normalClosure hst'.symm)).le⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStabGen_base

/-- **Rank step.**  If a finite `s ⊆ K₂(n, R)` has stabilization normally generating
`K₂(n+1, R)`, and `K₂(n+2, R) ≤ stab K₂(n+1, R)`, then `stab '' s ⊆ K₂(n+1, R)` is finite and its
stabilization normally generates `K₂(n+2, R)`. -/
theorem czStabGen_step
    (h : ∃ s : Set (St n R), s.Finite ∧ s ⊆ K2 (Fin n) R ∧
      K2 (Fin (n + 1)) R ≤ Subgroup.normalClosure (stab n R '' s))
    (hsurj : K2 (Fin (n + 1 + 1)) R ≤ (K2 (Fin (n + 1)) R).map (stab (n + 1) R)) :
    ∃ s' : Set (St (n + 1) R), s'.Finite ∧ s' ⊆ K2 (Fin (n + 1)) R ∧
      K2 (Fin (n + 1 + 1)) R ≤ Subgroup.normalClosure (stab (n + 1) R '' s') := by
  obtain ⟨s, hsfin, hsK, hle⟩ := h
  refine ⟨stab n R '' s, hsfin.image _, ?_, ?_⟩
  · rintro _ ⟨k, hk, rfl⟩
    exact (K2Stab n R ⟨k, hsK hk⟩).2
  · exact hsurj.trans ((Subgroup.map_mono hle).trans (Subgroup.map_normalClosure_le _ _))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStabGen_step

/-- Conversely, `T(n)` gives finite normal generation of `K₂(n+1, R)` in `St_{n+1}(R)`. -/
theorem czStabGen_fng_of_T
    (h : ∃ s : Set (St n R), s.Finite ∧ s ⊆ K2 (Fin n) R ∧
      K2 (Fin (n + 1)) R ≤ Subgroup.normalClosure (stab n R '' s)) :
    (K2 (Fin (n + 1)) R).IsFinitelyNormallyGenerated := by
  obtain ⟨s, hsfin, hsK, hle⟩ := h
  exact ⟨stab n R '' s, hsfin.image _,
    (normalClosure_eq_closure_of_subset_center (stab_image_subset_center hsK)).trans
      (closure_stab_image_eq_K2 hsK hle)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStabGen_fng_of_T

/-- Conversely, `T(n)` gives surjective stability `K₂(n+1, R) ≤ stab K₂(n, R)`. -/
theorem czStabGen_surj_of_T
    (h : ∃ s : Set (St n R), s.Finite ∧ s ⊆ K2 (Fin n) R ∧
      K2 (Fin (n + 1)) R ≤ Subgroup.normalClosure (stab n R '' s)) :
    K2 (Fin (n + 1)) R ≤ (K2 (Fin n) R).map (stab n R) := by
  obtain ⟨s, _, hsK, hle⟩ := h
  rw [← closure_stab_image_eq_K2 hsK hle, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact Subgroup.mem_map_of_mem (stab n R) (hsK hk)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStabGen_surj_of_T

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
