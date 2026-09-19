import GroupApproximation.BooneHigman.Metabelian.VdKStabRows
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Semilocal rings have stable range one

Lane `fix-bh-a`.  `stableRangeLE_one_of_finite_maximal`: if `R` has finitely many maximal ideals
then `sr(R) ≤ 1` (Bass's condition `vdkStab_StableRangeLE R 1`).  Local rings are the case of one
maximal ideal (`stableRangeLE_one_of_isLocalRing`).

Proof.  Let `(v₀, …, v_{n-1}, c)` be unimodular with `n ≥ 1`.  By the Chinese remainder theorem
for the pairwise coprime maximal ideals, choose `t` with `t ∈ 𝔪` when some `vⱼ ∉ 𝔪`, and
`t ≡ 1 (mod 𝔪)` otherwise.  Then no maximal ideal contains every entry of `(vⱼ + t c)ⱼ`: in the
first case `vⱼ + t c ≡ vⱼ`, and in the second `c ∉ 𝔪` (unimodularity) and `v₀ + t c ≡ c`.
-/

namespace GroupApproximation.StableRange

open GroupApproximation.BooneHigman.Metabelian.ElemFP

variable {R : Type*} [CommRing R]

/-- **Semilocal rings have stable range one.** -/
theorem stableRangeLE_one_of_finite_maximal (hfin : {M : Ideal R | M.IsMaximal}.Finite) :
    vdkStab_StableRangeLE R 1 := by
  classical
  intro n hn v hv
  haveI : Finite {M : Ideal R | M.IsMaximal} := hfin.to_subtype
  have hpair : Pairwise (IsCoprime on fun i : {M : Ideal R | M.IsMaximal} => (i : Ideal R)) := by
    intro i j hij
    haveI : (i : Ideal R).IsMaximal := i.2
    haveI : (j : Ideal R).IsMaximal := j.2
    exact Ideal.isCoprime_of_isMaximal fun h => hij (Subtype.ext h)
  obtain ⟨t, ht⟩ := Ideal.exists_forall_sub_mem_ideal hpair fun i =>
    if ∃ j : Fin n, v (Fin.castSucc j) ∉ (i : Ideal R) then (0 : R) else 1
  refine ⟨fun _ => t, (vdkStab_isUnimodular_iff _).mpr ?_⟩
  by_contra h1
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ ((Ideal.ne_top_iff_one _).mpr h1)
  have hmem : ∀ j : Fin n, v (Fin.castSucc j) + t * v (Fin.last n) ∈ M := fun j =>
    hle (Ideal.subset_span ⟨j, rfl⟩)
  have htM : t - (if ∃ j : Fin n, v (Fin.castSucc j) ∉ M then (0 : R) else 1) ∈ M :=
    ht ⟨M, hM⟩
  by_cases hA : ∃ j : Fin n, v (Fin.castSucc j) ∉ M
  · obtain ⟨j, hj⟩ := hA
    rw [if_pos ⟨j, hj⟩, sub_zero] at htM
    exact hj (by simpa using M.sub_mem (hmem j) (M.mul_mem_right (v (Fin.last n)) htM))
  · rw [if_neg hA] at htM
    have hA' : ∀ j : Fin n, v (Fin.castSucc j) ∈ M := fun j => by
      by_contra hj
      exact hA ⟨j, hj⟩
    have hc : v (Fin.last n) ∉ M := by
      intro hc
      apply hM.ne_top
      rw [Ideal.eq_top_iff_one]
      refine (Ideal.span_le.mpr ?_) ((vdkStab_isUnimodular_iff v).mp hv)
      rintro _ ⟨i, rfl⟩
      induction i using Fin.lastCases with
      | last => exact hc
      | cast j => exact hA' j
    have j0 : Fin n := ⟨0, by omega⟩
    apply hc
    have e : v (Fin.last n) = (v (Fin.castSucc j0) + t * v (Fin.last n)) - v (Fin.castSucc j0)
        - (t - 1) * v (Fin.last n) := by ring
    rw [e]
    exact M.sub_mem (M.sub_mem (hmem j0) (hA' j0)) (M.mul_mem_right _ htM)

#audit_axioms GroupApproximation.StableRange.stableRangeLE_one_of_finite_maximal

/-- **Local rings have stable range one.** -/
theorem stableRangeLE_one_of_isLocalRing [IsLocalRing R] : vdkStab_StableRangeLE R 1 :=
  stableRangeLE_one_of_finite_maximal <|
    (Set.finite_singleton (IsLocalRing.maximalIdeal R)).subset fun _ hM =>
      IsLocalRing.eq_maximalIdeal hM

#audit_axioms GroupApproximation.StableRange.stableRangeLE_one_of_isLocalRing

end GroupApproximation.StableRange
