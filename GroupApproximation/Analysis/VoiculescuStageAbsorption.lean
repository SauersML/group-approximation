import GroupApproximation.Analysis.VoiculescuStageEstimate

/-!
# The stage estimate, absorption half

`VoiculescuStageEstimate` shows one `improveUnit` step keeps asymptotic
centrality.  The recursion needs the other clause of `SequentialCompactUnit` to
improve along the same choices: the improved element must absorb compact
operators.

The identity is again `1 - improveUnit e f = g (1-f) g` with `g = √(1-e)`, so

    `T - improveUnit e f · T = (1 - improveUnit e f) T = g · (1-f) (g T)` ,

and `g T` is compact whenever `T` is.  So the whole thing is bounded by
`‖g‖ · ‖gT - f (gT)‖`, which tends to zero because the unit absorbs the compact
operator `g T`.  Note what is *not* needed: no bound on `‖g‖` — it is a constant
of the stage and multiplying a null sequence by it changes nothing — and no
relation between `T` and `e`.

So a single choice of `f` can be made to serve both clauses at once: the
centrality tolerance of the previous module and the absorption tolerance here
are two finite conditions on the same index, and `exists_improveUnit_stage`
below takes the maximum.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **The absorption half of the stage estimate.**  Along the unit, the improved
element absorbs any fixed compact operator. -/
theorem tendsto_norm_sub_improveUnit_mul (u : SequentialCompactUnit H)
    {e : H →L[ℂ] H} (he1 : e ≤ 1) (T : H →L[ℂ] H) (hT : IsCompactOperator T) :
    Tendsto (fun n ↦ ‖T - improveUnit e (u.toFun n) * T‖) atTop (𝓝 0) := by
  have hgT : IsCompactOperator ((CFC.sqrt (1 - e) * T : H →L[ℂ] H)) :=
    hT.clm_comp _
  have habs := u.tendsto_left (CFC.sqrt (1 - e) * T) hgT
  set q : H →L[ℂ] H := CFC.sqrt (1 - e) with hqdef
  have hbound : ∀ n, ‖T - improveUnit e (u.toFun n) * T‖
      ≤ ‖q‖ * ‖q * T - u.toFun n * (q * T)‖ := by
    intro n
    have hstep : T - improveUnit e (u.toFun n) * T
        = q * (q * T - u.toFun n * (q * T)) := by
      have h := one_sub_improveUnit (e := e) (f := u.toFun n) he1
      rw [hqdef]
      rw [show T - improveUnit e (u.toFun n) * T
          = (1 - improveUnit e (u.toFun n)) * T by rw [sub_mul, one_mul], h]
      noncomm_ring
    rw [hstep]
    exact norm_mul_le _ _
  refine squeeze_zero (fun n ↦ norm_nonneg _) hbound ?_
  simpa using habs.const_mul ‖q‖

/-- **One choice of `f` serves both clauses.**  For a finite family of targets, a
finite family of compacts, and any tolerance, some single member of the unit
improves `e` to an element that is that central and that absorbing. -/
theorem exists_improveUnit_stage (u : SequentialCompactUnit H)
    {e : H →L[ℂ] H} (he1 : e ≤ 1) (heK : IsCompactOperator e)
    (S : ℕ → (H →L[ℂ] H)) (T : ℕ → (H →L[ℂ] H))
    (hTK : ∀ i, IsCompactOperator (T i)) (F G : Finset ℕ)
    (hq : ∀ k, Tendsto (fun n ↦ ‖u.toFun n * S k - S k * u.toFun n‖) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n, (∀ k ∈ F,
        ‖improveUnit e (u.toFun n) * S k - S k * improveUnit e (u.toFun n)‖ < ε) ∧
      ∀ i ∈ G, ‖T i - improveUnit e (u.toFun n) * T i‖ < ε := by
  classical
  choose N hN using fun k : ℕ ↦ Metric.tendsto_atTop.1
    (tendsto_norm_commutator_improveUnit u he1 heK (S k) (hq k)) ε hε
  choose M hM using fun i : ℕ ↦ Metric.tendsto_atTop.1
    (tendsto_norm_sub_improveUnit_mul u he1 (T i) (hTK i)) ε hε
  refine ⟨max (F.sup N) (G.sup M), fun k hk ↦ ?_, fun i hi ↦ ?_⟩
  · have h := hN k (max (F.sup N) (G.sup M))
      (le_trans (Finset.le_sup hk) (le_max_left _ _))
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h
  · have h := hM i (max (F.sup N) (G.sup M))
      (le_trans (Finset.le_sup hi) (le_max_right _ _))
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h

end

end ShulmanFill
end GroupApproximation
