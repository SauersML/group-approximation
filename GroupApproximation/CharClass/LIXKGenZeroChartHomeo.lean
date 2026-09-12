import GroupApproximation.CharClass.LIXKGenSphereChartHomeo
import GroupApproximation.Meta.AxiomGuard

/-!
# The chart of `S^{2n+1}` at the `j`-th zero as a partial homeomorphism, at rank `n`

Lane `lix-oddside-n` (predecessor report `sp-oddside-n.md` §0.3a).

The chart at the `j`-th zero is `CharClass/LIXKGenChartZero.lean`'s `chartZeroVec n k j`, clamped
as in `CharClass/LIXKGenSphereChartHomeo.lean`.  Its inverse is `Ψ_k` followed by the inverse of the
chart at `−e₀`, so the whole partial homeomorphism is `κ_j` in coordinate `0` glued to the chart at
`−e₀`, and the two composition identities do the work:

* left inverse: `Ψ_k ∘ chart_j = chart at −e₀` (`psiVec_chartZeroVec`, no hypothesis);
* right inverse: `κ_j ∘ joinC k = id` on the sector (`kSect_joinC_of_mem_kSector`).

The target is `sphereNearZero n k j = {z | z₀ ∈ kSector k j ∧ Re (joinC k z₀) < 0}`, open by
continuity of `joinC k` and openness of the sector.

## Main results

* `KGen.psiSphere`, `psiSphere_mem_sphereLowerZero`.
* `KGen.sphereNearZero`, `isOpen_sphereNearZero`.
* `KGen.zeroChartHomeo n k j` — **the chart at the `j`-th zero as an `OpenPartialHomeomorph`**,
  with `zeroChartHomeo_zero = kZero n k j` and `psiSphere_zeroChartHomeo`
  (`Ψ_k ∘ chart_j = chart at −e₀` on the source).
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace KGen

open Set
open GroupApproximation.STW59
open GroupApproximation.LIX.Powers

set_option linter.unusedSectionVars false

/-! ## 1. `Ψ_k` on the sphere, and the target -/

/-- `Ψ_k` as a map of the sphere. -/
def psiSphere (n k : ℕ) (z : ↥(unitVectors (Fin (n + 1)))) : ↥(unitVectors (Fin (n + 1))) :=
  ⟨psiVec n k z, psiVec_mem_unitVectors z.2⟩

theorem continuous_psiSphere (n k : ℕ) : Continuous (psiSphere n k) :=
  ((continuous_psiVec n k).comp continuous_subtype_val).subtype_mk _

theorem psiSphere_mem_sphereLowerZero {n k : ℕ} {z : ↥(unitVectors (Fin (n + 1)))}
    (hz : (joinC k ((z : Fin (n + 1) → ℂ) 0)).re < 0) :
    psiSphere n k z ∈ sphereLowerZero n := by
  show ((psiVec n k (z : Fin (n + 1) → ℂ)) 0).re < 0
  rw [psiVec_apply_zero]
  exact hz

/-- The neighbourhood of the `j`-th zero the chart lands in. -/
def sphereNearZero (n k : ℕ) (j : Fin (k + 1)) : Set ↥(unitVectors (Fin (n + 1))) :=
  {z | (z : Fin (n + 1) → ℂ) 0 ∈ kSector k j ∧ (joinC k ((z : Fin (n + 1) → ℂ) 0)).re < 0}

theorem isOpen_sphereNearZero (n k : ℕ) (j : Fin (k + 1)) : IsOpen (sphereNearZero n k j) := by
  have hc : Continuous fun z : ↥(unitVectors (Fin (n + 1))) => (z : Fin (n + 1) → ℂ) 0 :=
    (continuous_apply 0).comp continuous_subtype_val
  have h1 : IsOpen {z : ↥(unitVectors (Fin (n + 1))) | (z : Fin (n + 1) → ℂ) 0 ∈ kSector k j} :=
    (isOpen_kSector k j).preimage hc
  have h2 : IsOpen
      {z : ↥(unitVectors (Fin (n + 1))) | (joinC k ((z : Fin (n + 1) → ℂ) 0)).re < 0} :=
    isOpen_lt (Complex.continuous_re.comp ((continuous_joinC k).comp hc)) continuous_const
  exact h1.inter h2

/-! ## 2. The chart and its inverse -/

/-- The chart at the `j`-th zero, total. -/
def zeroChartFun (n k : ℕ) (j : Fin (k + 1)) (w : ChartBase n) : ↥(unitVectors (Fin (n + 1))) :=
  ⟨chartZeroVec n k j (chartClamp n w), chartZeroVec_mem (chartQ_clamp_le_one n w)⟩

/-- Its inverse: `Ψ_k`, then the inverse of the chart at `−e₀`. -/
def zeroChartInv (n k : ℕ) (_j : Fin (k + 1)) (z : ↥(unitVectors (Fin (n + 1)))) : ChartBase n :=
  sphereChartInv n (psiSphere n k z)

/-- **`Ψ_k ∘ chart_j = chart at −e₀`, as maps into the sphere.** -/
theorem psiSphere_zeroChartFun (n k : ℕ) (j : Fin (k + 1)) (w : ChartBase n) :
    psiSphere n k (zeroChartFun n k j w) = sphereChartFun n w :=
  Subtype.ext (psiVec_chartZeroVec n k j (chartClamp n w))

/-- **The chart at the `j`-th zero, as a partial homeomorphism.** -/
def zeroChartHomeo (n k : ℕ) (j : Fin (k + 1)) :
    OpenPartialHomeomorph (ChartBase n) ↥(unitVectors (Fin (n + 1))) where
  toFun := zeroChartFun n k j
  invFun := zeroChartInv n k j
  source := {w | chartQ n w < 1}
  target := sphereNearZero n k j
  map_source' := by
    intro w hw
    have hw' : chartQ n w < 1 := hw
    show chartZeroVec n k j (chartClamp n w) 0 ∈ kSector k j
      ∧ (joinC k (chartZeroVec n k j (chartClamp n w) 0)).re < 0
    rw [chartClamp_eq_self hw'.le]
    refine ⟨chartZeroVec_zero_mem_kSector j hw', ?_⟩
    rw [chartZeroVec_apply_zero, joinC_kSect]
    exact re_sphereChartVec_zero_neg hw'
  map_target' := by
    intro z hz
    have hz2 : (joinC k ((z : Fin (n + 1) → ℂ) 0)).re < 0 := hz.2
    exact (sphereChartHomeo n).map_target (psiSphere_mem_sphereLowerZero hz2)
  left_inv' := by
    intro w hw
    show sphereChartInv n (psiSphere n k (zeroChartFun n k j w)) = w
    rw [psiSphere_zeroChartFun]
    exact (sphereChartHomeo n).left_inv hw
  right_inv' := by
    intro z hz
    have hz1 : (z : Fin (n + 1) → ℂ) 0 ∈ kSector k j := hz.1
    have hz2 : (joinC k ((z : Fin (n + 1) → ℂ) 0)).re < 0 := hz.2
    have hr := (sphereChartHomeo n).right_inv (psiSphere_mem_sphereLowerZero hz2)
    have hr' : sphereChartVec n (chartClamp n (zeroChartInv n k j z)) = psiVec n k z :=
      congrArg (fun y : ↥(unitVectors (Fin (n + 1))) => (y : Fin (n + 1) → ℂ)) hr
    refine Subtype.ext ?_
    show chartZeroVec n k j (chartClamp n (zeroChartInv n k j z)) = (z : Fin (n + 1) → ℂ)
    funext i
    rcases eq_or_ne i 0 with rfl | hi
    · rw [chartZeroVec_apply_zero, hr', psiVec_apply_zero, kSect_joinC_of_mem_kSector hz1]
    · rw [chartZeroVec_apply_of_ne n k j _ hi, hr', psiVec_apply_of_ne n k _ hi]
  open_source := isOpen_lt (continuous_chartQ n) continuous_const
  open_target := isOpen_sphereNearZero n k j
  continuousOn_toFun := by
    refine (Topology.IsInducing.subtypeVal.continuousOn_iff (f := zeroChartFun n k j)).mpr ?_
    refine (continuousOn_chartZeroVec n k j).congr fun w hw => ?_
    have hw' : chartQ n w < 1 := hw
    show chartZeroVec n k j (chartClamp n w) = chartZeroVec n k j w
    rw [chartClamp_eq_self hw'.le]
  continuousOn_invFun :=
    ((continuous_sphereChartInv n).comp (continuous_psiSphere n k)).continuousOn

theorem zero_mem_zeroChartHomeo_source (n k : ℕ) (j : Fin (k + 1)) :
    (0 : ChartBase n) ∈ (zeroChartHomeo n k j).source := by
  show chartQ n 0 < 1
  simp [chartQ]

/-- The chart at the `j`-th zero is centred there. -/
theorem zeroChartHomeo_zero (n k : ℕ) (j : Fin (k + 1)) :
    zeroChartHomeo n k j 0 = kZero n k j := by
  refine Subtype.ext ?_
  show chartZeroVec n k j (chartClamp n 0) = kZeroVec n k j
  rw [chartClamp_eq_self (by simp [chartQ]), chartZeroVec_zero]

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.isOpen_sphereNearZero
#audit_axioms KGen.psiSphere_zeroChartFun
#audit_axioms KGen.zeroChartHomeo_zero

end GroupApproximation.CharClass
