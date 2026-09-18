import GroupApproximation.BooneHigman.Metabelian.VdKInjDirectRow
import GroupApproximation.Meta.AxiomGuard

/-!
# Elementary transitivity on unimodular rows under a stable-range bound

Lane `bh-met-91e`, second step of van der Kallen's elementary route.  Let `R` be commutative with
`sr(R) ≤ r` (`vdkStab_StableRangeLE R r`) and let `n ≥ r`.  Every unimodular row
`u : Fin (n + 1) → R` is reached from `e_last` by some `g : St_{n+1}(R)`
(`vdkInjDirect_reach_of_stableRange`).  The proof is the classical three moves:

1. **reduce** (`vdkInjDirect_reach_reduce`): add `u_last b_k` to coordinate `k` with the roots
   `x_{last,k}(b_k)`.  The first `n` coordinates then form a unimodular row, by the stable
   range condition via `vdkStab_reduceRow`.
2. **last coordinate one** (`vdkInjDirect_reach_lastOne`): with `∑ v_k w_k = 1`, the roots
   `x_{k,last}(w_k (1 - v_last))` move `v_last` to `1`.
3. **clear** (`vdkInjDirect_reach_clear`): the roots `x_{last,k}(-v_k)` kill the first `n`
   coordinates.

The moves are then inverted with `vdkInjDirect_reach_symm`.  The packaged form is
`vdkInjDirect_rowTransitive_of_stableRange : vdkInjDirect_RowTransitive R r`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open scoped Matrix

section Moves

variable {R : Type*} [CommRing R] {n : ℕ}

theorem vdkInjDirect_sumSingle_castSucc (f : Fin n → R) (i : Fin n) :
    (∑ k : Fin n, (Pi.single k.castSucc (f k) : Fin (n + 1) → R)) i.castSucc = f i := by
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · exact Pi.single_eq_same _ _
  · intro k _ hk
    exact Pi.single_eq_of_ne (fun h => hk (Fin.castSucc_inj.mp h).symm) _
  · intro hi
    exact absurd (Finset.mem_univ i) hi

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjDirect_sumSingle_castSucc

theorem vdkInjDirect_sumSingle_castSucc_last (f : Fin n → R) :
    (∑ k : Fin n, (Pi.single k.castSucc (f k) : Fin (n + 1) → R)) (Fin.last n) = 0 := by
  rw [Finset.sum_apply]
  exact Finset.sum_eq_zero fun k _ => Pi.single_eq_of_ne (Fin.castSucc_ne_last k).symm _

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjDirect_sumSingle_castSucc_last

theorem vdkInjDirect_sumSingle_last_last (f : Fin n → R) :
    (∑ k : Fin n, (Pi.single (Fin.last n) (f k) : Fin (n + 1) → R)) (Fin.last n) =
      ∑ k : Fin n, f k := by
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl fun k _ => Pi.single_eq_same _ _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjDirect_sumSingle_last_last

/-- **Move 1**: after the reduction, the first `n` coordinates form a unimodular row. -/
theorem vdkInjDirect_reach_reduce {r : ℕ} (hsr : vdkStab_StableRangeLE R r) (hn : r ≤ n)
    (u : Fin (n + 1) → R) (hu : vdkStab_IsUnimodular u) :
    ∃ v : Fin (n + 1) → R, vdkInjDirect_Reach u v ∧
      ∃ w : Fin n → R, ∑ k : Fin n, v k.castSucc * w k = 1 := by
  obtain ⟨b, w, hw⟩ := hsr n hn u hu
  have h : vdkInjDirect_Reach u (u + ∑ k : Fin n,
      (Pi.single k.castSucc (u (Fin.last n) * b k) : Fin (n + 1) → R)) :=
    vdkInjDirect_reach_add_sum Finset.univ u (fun _ => Fin.last n) Fin.castSucc
      (fun _ l => Fin.castSucc_ne_last l) b
  refine ⟨_, h, w, ?_⟩
  rw [← hw]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.add_apply, vdkInjDirect_sumSingle_castSucc, vdkStab_reduceRow_apply]
  ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjDirect_reach_reduce

/-- **Move 2**: if the first `n` coordinates are unimodular, the last one can be made `1`. -/
theorem vdkInjDirect_reach_lastOne (v : Fin (n + 1) → R) (w : Fin n → R)
    (hw : ∑ k : Fin n, v k.castSucc * w k = 1) :
    ∃ v' : Fin (n + 1) → R, vdkInjDirect_Reach v v' ∧ v' (Fin.last n) = 1 := by
  have h : vdkInjDirect_Reach v (v + ∑ k : Fin n,
      (Pi.single (Fin.last n) (v k.castSucc * (w k * (1 - v (Fin.last n)))) :
        Fin (n + 1) → R)) :=
    vdkInjDirect_reach_add_sum Finset.univ v Fin.castSucc (fun _ => Fin.last n)
      (fun k _ => (Fin.castSucc_ne_last k).symm) (fun k => w k * (1 - v (Fin.last n)))
  refine ⟨_, h, ?_⟩
  have hs : ∑ k : Fin n, v k.castSucc * (w k * (1 - v (Fin.last n))) =
      1 - v (Fin.last n) := by
    calc ∑ k : Fin n, v k.castSucc * (w k * (1 - v (Fin.last n)))
        = (∑ k : Fin n, v k.castSucc * w k) * (1 - v (Fin.last n)) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => (mul_assoc _ _ _).symm
      _ = 1 - v (Fin.last n) := by rw [hw, one_mul]
  rw [Pi.add_apply, vdkInjDirect_sumSingle_last_last, hs]
  ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjDirect_reach_lastOne

/-- **Move 3**: a row with last coordinate `1` is carried to `e_last`. -/
theorem vdkInjDirect_reach_clear (v : Fin (n + 1) → R) (hv : v (Fin.last n) = 1) :
    vdkInjDirect_Reach v (Pi.single (Fin.last n) 1 : Fin (n + 1) → R) := by
  have h : vdkInjDirect_Reach v (v + ∑ k : Fin n,
      (Pi.single k.castSucc (v (Fin.last n) * -v k.castSucc) : Fin (n + 1) → R)) :=
    vdkInjDirect_reach_add_sum Finset.univ v (fun _ => Fin.last n) Fin.castSucc
      (fun _ l => Fin.castSucc_ne_last l) (fun k => -v k.castSucc)
  have key : v + ∑ k : Fin n,
      (Pi.single k.castSucc (v (Fin.last n) * -v k.castSucc) : Fin (n + 1) → R) =
        Pi.single (Fin.last n) 1 := by
    funext j
    induction j using Fin.lastCases with
    | last =>
      rw [Pi.add_apply, vdkInjDirect_sumSingle_castSucc_last, add_zero, hv, Pi.single_eq_same]
    | cast i =>
      rw [Pi.add_apply, vdkInjDirect_sumSingle_castSucc, hv, one_mul, add_neg_cancel,
        Pi.single_eq_of_ne (Fin.castSucc_ne_last i)]
  rw [key] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjDirect_reach_clear

/-- **Transitivity**: under `sr(R) ≤ r ≤ n`, `St_{n+1}(R)` carries `e_last` to every
unimodular row of length `n + 1`. -/
theorem vdkInjDirect_reach_of_stableRange {r : ℕ} (hsr : vdkStab_StableRangeLE R r)
    (hn : r ≤ n) (u : Fin (n + 1) → R) (hu : vdkStab_IsUnimodular u) :
    vdkInjDirect_Reach (Pi.single (Fin.last n) 1 : Fin (n + 1) → R) u := by
  obtain ⟨v, huv, w, hw⟩ := vdkInjDirect_reach_reduce hsr hn u hu
  obtain ⟨v', hvv', hv'⟩ := vdkInjDirect_reach_lastOne v w hw
  exact vdkInjDirect_reach_symm (vdkInjDirect_reach_trans huv
    (vdkInjDirect_reach_trans hvv' (vdkInjDirect_reach_clear v' hv')))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjDirect_reach_of_stableRange

end Moves

/-- Elementary transitivity on unimodular rows of every length `m + 1` with `m ≥ r`. -/
def vdkInjDirect_RowTransitive (R : Type*) [CommRing R] (r : ℕ) : Prop :=
  ∀ m : ℕ, r ≤ m → ∀ u : Fin (m + 1) → R, vdkStab_IsUnimodular u →
    vdkInjDirect_Reach (Pi.single (Fin.last m) 1 : Fin (m + 1) → R) u

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjDirect_RowTransitive

/-- **Proved**: `sr(R) ≤ r` gives elementary transitivity on unimodular rows of length `> r`. -/
theorem vdkInjDirect_rowTransitive_of_stableRange {R : Type*} [CommRing R] {r : ℕ}
    (hsr : vdkStab_StableRangeLE R r) : vdkInjDirect_RowTransitive R r :=
  fun _ hm u hu => vdkInjDirect_reach_of_stableRange hsr hm u hu

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjDirect_rowTransitive_of_stableRange

end GroupApproximation.BooneHigman.Metabelian.ElemFP
