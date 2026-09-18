import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngGtOneRank3Map
import GroupApproximation.Meta.AxiomGuard

/-!
# `czK2FngGtOne_RankThreeStatement` by induction on the primes (lane `bh-met-93s`, part 2)

**The one-prime step.**  `czK2FngGtOneRank3_StepStatement` says the following.  Let `m > 0`,
let `p` be prime, and let `φ : ℤ[1/m] → ℤ[1/(mp)]` be the localisation map.  Then
`K₂(3, ℤ[1/(mp)])` lies in the normal closure of `φ(K₂(3, ℤ[1/m]))` together with finitely many
elements of `K₂(3, ℤ[1/(mp)])`.

**Proved outright.**
* `czK2FngGtOneRank3_fng_all_of_step`: the step gives `K₂(3, ℤ[1/n])` finitely normally
  generated for every `n > 0`.  The proof is a strong induction on `n`.  The base `n = 1` is
  `czK2FngTorus_k2ThreeOne_fng`, which rests on the repository's own `SL_3(ℤ)` presentation
  (`P13`).  For `n ≠ 1`, write `n = c · p` with `p = minFac n`, then use the step and
  `czK2FngGtOneRank3_fng_of_step`.
* `czK2FngGtOneRank3_rankThree_of_step`: the step gives `czK2FngGtOne_RankThreeStatement`.
* `czK2FngGtOneRank3_step_of_rankThree`: the converse.

**Strength (LOUD).  The step is logically EQUIVALENT to `czK2FngGtOne_RankThreeStatement`.**
Both directions are proved here.  It is therefore not the residual of this lane.  The residual
is the coset statement `czK2FngGtOneRank3_CosetStatement` (module `...Rank3Coset`), which
implies the step.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

/-- **The one-prime step.**  For `m > 0` and `p` prime, `K₂(3, ℤ[1/(mp)])` lies in the normal
closure of the image of `K₂(3, ℤ[1/m])` together with a finite subset of `K₂(3, ℤ[1/(mp)])`.
It is logically equivalent to `czK2FngGtOne_RankThreeStatement`
(`czK2FngGtOneRank3_rankThree_of_step`, `czK2FngGtOneRank3_step_of_rankThree`). -/
def czK2FngGtOneRank3_StepStatement : Prop :=
  ∀ m p : ℕ, 0 < m → p.Prime →
    ∃ s : Set (SteinbergGroup (Fin 3) (Localization.Away ((m * p : ℕ) : ℤ))), s.Finite ∧
      s ⊆ K2 (Fin 3) (Localization.Away ((m * p : ℕ) : ℤ)) ∧
      K2 (Fin 3) (Localization.Away ((m * p : ℕ) : ℤ)) ≤ Subgroup.normalClosure
        (ringMap (czK2FngGtOneRank3_locMap m p) ''
          (K2 (Fin 3) (Localization.Away (m : ℤ)) :
            Set (SteinbergGroup (Fin 3) (Localization.Away (m : ℤ)))) ∪ s)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngGtOneRank3_StepStatement

/-- **Prime induction.**  The one-prime step gives `K₂(3, ℤ[1/n])` finitely normally generated
for every `n > 0`.  The base case `n = 1` is proved outright. -/
theorem czK2FngGtOneRank3_fng_all_of_step (h : czK2FngGtOneRank3_StepStatement) :
    ∀ n : ℕ, 0 < n → (K2 (Fin 3) (Localization.Away (n : ℤ))).IsFinitelyNormallyGenerated := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases h1 : n = 1
    · subst h1
      exact czK2FngTorus_k2ThreeOne_fng
    · obtain ⟨p, hp, c, rfl⟩ : ∃ p : ℕ, p.Prime ∧ ∃ c : ℕ, n = c * p :=
        ⟨n.minFac, Nat.minFac_prime h1, n / n.minFac,
          (Nat.div_mul_cancel (Nat.minFac_dvd n)).symm⟩
      have hcpos : 0 < c := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at hn
      have hclt : c < c * p := (lt_mul_iff_one_lt_right hcpos).mpr hp.one_lt
      exact czK2FngGtOneRank3_fng_of_step (czK2FngGtOneRank3_locMap c p)
        (ih c hclt hcpos) (h c p hcpos hp)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngGtOneRank3_fng_all_of_step

/-- **The reduction.**  The one-prime step gives `czK2FngGtOne_RankThreeStatement`. -/
theorem czK2FngGtOneRank3_rankThree_of_step (h : czK2FngGtOneRank3_StepStatement) :
    czK2FngGtOne_RankThreeStatement :=
  fun m hm ↦ czK2FngGtOneRank3_fng_all_of_step h m (by omega)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngGtOneRank3_rankThree_of_step

/-- **The converse (LOUD: the step is equivalent to the target).**
`czK2FngGtOne_RankThreeStatement` gives the one-prime step: take `s` to be a finite normal
generating set of `K₂(3, ℤ[1/(mp)])`. -/
theorem czK2FngGtOneRank3_step_of_rankThree (h : czK2FngGtOne_RankThreeStatement) :
    czK2FngGtOneRank3_StepStatement := by
  intro m p hm hp
  have hmp : 1 < m * p := lt_of_lt_of_le hp.one_lt (Nat.le_mul_of_pos_left p hm)
  obtain ⟨s, hsfin, hs⟩ := h (m * p) hmp
  refine ⟨s, hsfin, ?_, ?_⟩
  · rw [← hs]
    exact Subgroup.subset_normalClosure
  · rw [← hs]
    exact Subgroup.normalClosure_mono Set.subset_union_right

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngGtOneRank3_step_of_rankThree

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
