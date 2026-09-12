import GroupApproximation.Analysis.VoiculescuStageAbsorption
import GroupApproximation.Analysis.VoiculescuUnitStrongLimit

/-!
# The stage estimate, vector half, and the complete stage map

The recursion has to deliver a unit converging strongly to the identity, and it
is cheaper to arrange that directly than to arrange norm absorption against a
dense family of compact operators — which would need the compacts to be
separable, a fact the tree does not have and, it turns out, does not need.
Strong convergence plus the landed
`VoiculescuStrongToNorm.strongToNormOnCompacts` gives the norm absorption back,
so nothing is lost by taking the cheaper route.

The estimate is the same identity once more.  With `g = √(1-e)`,

    `x - improveUnit e f · x = (1 - improveUnit e f) x = g ((1-f) (g x))` ,

bounded by `‖g‖ ‖f (g x) - g x‖`, which tends to zero because the unit converges
strongly at the vector `g x` (`SequentialCompactUnit.tendsto_apply`).  As with
the other two halves no bound on `‖g‖` is needed and no relation between `x` and
`e` is needed, so the stage is again free to aim at any tolerance.

`exists_improveUnit_stage_full` is the complete stage map of the recursion: a
finite family of targets, a finite family of compact operators, a finite family
of vectors, one tolerance, and one member of the unit meeting all of it.  The
vectors are where separability of the space is spent — the recursion feeds it
prefixes of a dense sequence.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **The vector half of the stage estimate.**  Along the unit, the improved
element moves any fixed vector arbitrarily little. -/
theorem tendsto_norm_sub_improveUnit_apply (u : SequentialCompactUnit H)
    {e : H →L[ℂ] H} (he1 : e ≤ 1) (x : H) :
    Tendsto (fun n ↦ ‖x - improveUnit e (u.toFun n) x‖) atTop (𝓝 0) := by
  have hstrong := u.tendsto_apply (CFC.sqrt (1 - e) x)
  rw [tendsto_iff_norm_sub_tendsto_zero] at hstrong
  set q : H →L[ℂ] H := CFC.sqrt (1 - e) with hqdef
  have hb : ∀ n, ‖x - improveUnit e (u.toFun n) x‖
      ≤ ‖q‖ * ‖u.toFun n (q x) - q x‖ := by
    intro n
    have h := one_sub_improveUnit (e := e) (f := u.toFun n) he1
    rw [← hqdef] at h
    have hx : x - improveUnit e (u.toFun n) x
        = (1 - improveUnit e (u.toFun n)) x := rfl
    rw [hx, h]
    have hval : (q * (1 - u.toFun n) * q) x = -(q (u.toFun n (q x) - q x)) := by
      show q (q x - u.toFun n (q x)) = -(q (u.toFun n (q x) - q x))
      rw [← map_neg, neg_sub]
    rw [hval, norm_neg]
    exact q.le_opNorm _
  exact squeeze_zero (fun n ↦ norm_nonneg _) hb
    (by simpa using hstrong.const_mul ‖q‖)

/-- **The complete stage map.**  One member of the unit that is simultaneously
central enough against a finite family of targets, absorbing enough against a
finite family of compacts, and close enough to the identity on a finite family
of vectors. -/
theorem exists_improveUnit_stage_full (u : SequentialCompactUnit H)
    {e : H →L[ℂ] H} (he1 : e ≤ 1) (heK : IsCompactOperator e)
    (S : ℕ → (H →L[ℂ] H)) (T : ℕ → (H →L[ℂ] H))
    (hTK : ∀ i, IsCompactOperator (T i)) (x : ℕ → H)
    (F G J : Finset ℕ)
    (hq : ∀ k, Tendsto (fun n ↦ ‖u.toFun n * S k - S k * u.toFun n‖) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n, (∀ k ∈ F,
        ‖improveUnit e (u.toFun n) * S k - S k * improveUnit e (u.toFun n)‖ < ε) ∧
      (∀ i ∈ G, ‖T i - improveUnit e (u.toFun n) * T i‖ < ε) ∧
      ∀ j ∈ J, ‖x j - improveUnit e (u.toFun n) (x j)‖ < ε := by
  classical
  choose N hN using fun k : ℕ ↦ Metric.tendsto_atTop.1
    (tendsto_norm_commutator_improveUnit u he1 heK (S k) (hq k)) ε hε
  choose M hM using fun i : ℕ ↦ Metric.tendsto_atTop.1
    (tendsto_norm_sub_improveUnit_mul u he1 (T i) (hTK i)) ε hε
  choose P hP using fun j : ℕ ↦ Metric.tendsto_atTop.1
    (tendsto_norm_sub_improveUnit_apply u he1 (x j)) ε hε
  refine ⟨max (max (F.sup N) (G.sup M)) (J.sup P), fun k hk ↦ ?_, fun i hi ↦ ?_,
    fun j hj ↦ ?_⟩
  · have h := hN k (max (max (F.sup N) (G.sup M)) (J.sup P))
      (le_trans (le_trans (Finset.le_sup hk) (le_max_left _ _)) (le_max_left _ _))
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h
  · have h := hM i (max (max (F.sup N) (G.sup M)) (J.sup P))
      (le_trans (le_trans (Finset.le_sup hi) (le_max_right _ _)) (le_max_left _ _))
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h
  · have h := hP j (max (max (F.sup N) (G.sup M)) (J.sup P))
      (le_trans (Finset.le_sup hj) (le_max_right _ _))
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h

end

end ShulmanFill
end GroupApproximation
