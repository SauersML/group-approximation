import GroupApproximation.Analysis.GroupVonNeumannAlgebra

/-!
# The canonical trace on the group von Neumann algebra, and finiteness

Third module of the `LI.06d` lane (`p:limits-trace`).  The sentence's witness
must be a II₁ factor: infinite-dimensional, a factor, and **finite**, with the
finiteness coming from a faithful trace.  This module builds the trace on
`L(G)` and proves everything the II₁ assembly needs, by transporting the
coefficient computations of `Analysis/ReducedGroupCStarTraceFaithful.lean`
from the reduced C\*-algebra to the von Neumann algebra: every proof there
consumed only commutation with the right translations, which elements of
`L(G) = λ(G)''` satisfy because the right regular image lies in `λ(G)'`.

The trace is the identity coefficient `τ(T) = (Tδ₁)(1) = ⟪δ₁, Tδ₁⟫`.

* `apply_single_of_mem` — an element of `L(G)` acts on point masses by right
  translation of its coefficient vector.
* `hasSum_product_coefficient_of_mem` — the convolution formula for `τ(TS)`.
* `coefficient_mul_comm` — **traciality**, by the inversion reindexing.
* `coefficient_star_mul_self` — `τ(T⋆T) = ‖Tδ₁‖²`.
* `eq_zero_of_mem_of_apply_deltaOne_eq_zero` — `δ₁` is separating for
  `L(G)`; with the previous item, the trace is **faithful**.
* `mul_star_eq_one_of_star_mul_eq_one` — **finiteness**: an isometry of
  `L(G)` is a unitary, because `1 − vv⋆` is a projection of trace zero.
-/

namespace GroupApproximation
namespace GroupVonNeumann

open ReducedGroupCStarTrace TwoSidedRegularCommutant
open scoped ENNReal InnerProductSpace

noncomputable section

universe u

variable (G : Type u) [Group G]

local instance : DecidableEq G := Classical.decEq G

/-! ## Coordinate facts about `δ₁` -/

/-- Left translation of the identity point mass, at the ambient level. -/
theorem leftRegularOperator_deltaOne (g : G) :
    leftRegularOperator G g (deltaOne G) = lp.single 2 g 1 := by
  apply lp.ext
  funext x
  simp only [leftRegularOperator_apply, deltaOne, lp.coeFn_single]
  by_cases hx : x = g
  · subst hx
    simp
  · have hne : g⁻¹ * x ≠ 1 := by
      intro h
      apply hx
      calc x = g * (g⁻¹ * x) := by simp
        _ = g := by rw [h, mul_one]
    rw [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hx]

/-- The identity point mass is a unit vector. -/
theorem norm_deltaOne : ‖deltaOne G‖ = 1 := by
  have h : ⟪deltaOne G, deltaOne G⟫_ℂ = 1 := by
    rw [deltaOne, lp.inner_single_left]
    simp
  have h2 : ((‖deltaOne G‖ : ℂ)) ^ 2 = 1 := by
    have h3 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (deltaOne G)
    rw [h] at h3
    exact h3.symm
  have h3 : ‖deltaOne G‖ ^ 2 = 1 := by
    exact_mod_cast h2
  nlinarith [norm_nonneg (deltaOne G)]

/-- The trace of the identity is `1`, in coefficient form. -/
theorem coefficient_one :
    ((1 : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)) 1 = 1 := by
  change deltaOne G 1 = 1
  exact deltaOne_apply_self G

/-! ## The coefficient calculus for members of `L(G)` -/

/-- An element of `L(G)` acts on a point mass by right-translating its
coefficient vector. -/
theorem apply_single_of_mem {T : GroupHilbert G →L[ℂ] GroupHilbert G}
    (hT : T ∈ groupVonNeumannAlgebra G) (g : G) (c : ℂ) :
    T (lp.single 2 g c) = c • rightRegularOperator G g (T (deltaOne G)) := by
  have hsingle : (lp.single 2 g c : GroupHilbert G) =
      c • (lp.single 2 g (1 : ℂ) : GroupHilbert G) := by
    rw [← lp.single_smul]
    simp
  rw [hsingle, map_smul, ← rightRegular_deltaOne]
  congr 1
  exact (DFunLike.congr_fun (commutes_rightRegularOperator G hT g)
    (deltaOne G)).symm

/-- **The convolution formula.**  For `T ∈ L(G)` and any bounded `S`, the
identity coefficient of `T ∘ S` is the convolution of the two coefficient
columns. -/
theorem hasSum_product_coefficient_of_mem
    {T : GroupHilbert G →L[ℂ] GroupHilbert G}
    (hT : T ∈ groupVonNeumannAlgebra G)
    (S : GroupHilbert G →L[ℂ] GroupHilbert G) :
    HasSum
      (fun g : G ↦ (S (deltaOne G)) g * (T (deltaOne G)) g⁻¹)
      (((T * S) (deltaOne G)) 1) := by
  let evalAfterT : GroupHilbert G →L[ℂ] ℂ :=
    (lp.evalCLM ℂ (fun _ : G ↦ ℂ) 2 (1 : G)).comp T
  have hs := (lp.hasSum_single ENNReal.ofNat_ne_top (S (deltaOne G))).mapL
    evalAfterT
  convert hs using 1
  · ext g
    dsimp only [evalAfterT, ContinuousLinearMap.comp_apply]
    change (S (deltaOne G)) g * (T (deltaOne G)) g⁻¹
      = (T (lp.single 2 g ((S (deltaOne G)) g))) 1
    rw [apply_single_of_mem G hT]
    change (S (deltaOne G)) g * (T (deltaOne G)) g⁻¹
      = (S (deltaOne G)) g *
        (rightRegularOperator G g (T (deltaOne G))) 1
    rw [rightRegularOperator_apply]
    simp only [one_mul]
  · rfl

/-- **Traciality.**  The identity coefficient is a trace on `L(G)`: the two
convolutions are exchanged by the inversion bijection of the group. -/
theorem coefficient_mul_comm
    {T S : GroupHilbert G →L[ℂ] GroupHilbert G}
    (hT : T ∈ groupVonNeumannAlgebra G)
    (hS : S ∈ groupVonNeumannAlgebra G) :
    ((T * S) (deltaOne G)) 1 = ((S * T) (deltaOne G)) 1 := by
  have hTS := hasSum_product_coefficient_of_mem G hT S
  have hST := hasSum_product_coefficient_of_mem G hS T
  have hSTinv := (Equiv.inv G).hasSum_iff.mpr hST
  apply hTS.unique
  convert hSTinv using 1
  ext g
  simp only [Function.comp_apply, Equiv.inv_apply, inv_inv]
  rw [mul_comm]

/-- `τ(T⋆T) = ‖Tδ₁‖²`, for any bounded operator. -/
theorem coefficient_star_mul_self (T : GroupHilbert G →L[ℂ] GroupHilbert G) :
    ((star T * T) (deltaOne G)) 1 = (‖T (deltaOne G)‖ : ℂ) ^ 2 := by
  calc ((star T * T) (deltaOne G)) 1
      = ⟪deltaOne G, (star T * T) (deltaOne G)⟫_ℂ := by
        rw [deltaOne, lp.inner_single_left]
        simp
    _ = (‖T (deltaOne G)‖ : ℂ) ^ 2 := by
        simp only [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
          ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
        rfl

/-! ## Separation and faithfulness -/

/-- **`δ₁` separates `L(G)`.** -/
theorem eq_zero_of_mem_of_apply_deltaOne_eq_zero
    {T : GroupHilbert G →L[ℂ] GroupHilbert G}
    (hT : T ∈ groupVonNeumannAlgebra G)
    (h : T (deltaOne G) = 0) : T = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  have hs := (lp.hasSum_single ENNReal.ofNat_ne_top f).mapL T
  have hzero : ∀ g : G, T (lp.single 2 g (f g)) = 0 := by
    intro g
    rw [apply_single_of_mem G hT, h, map_zero, smul_zero]
  have hz : HasSum (fun g : G ↦ T (lp.single 2 g (f g))) 0 := by
    simpa only [hzero] using
      (hasSum_zero : HasSum (fun _ : G ↦ (0 : GroupHilbert G)) 0)
  exact hs.unique hz

/-- **Faithfulness of the trace on `L(G)`.** -/
theorem eq_zero_of_mem_of_coefficient_star_mul_self_eq_zero
    {T : GroupHilbert G →L[ℂ] GroupHilbert G}
    (hT : T ∈ groupVonNeumannAlgebra G)
    (h : ((star T * T) (deltaOne G)) 1 = 0) : T = 0 := by
  rw [coefficient_star_mul_self] at h
  have hnorm : ‖T (deltaOne G)‖ = 0 := by
    have hc : (‖T (deltaOne G)‖ : ℂ) = 0 := sq_eq_zero_iff.mp h
    exact Complex.ofReal_eq_zero.mp hc
  exact eq_zero_of_mem_of_apply_deltaOne_eq_zero G hT (norm_eq_zero.mp hnorm)

/-! ## Finiteness -/

/-- **`L(G)` is a finite von Neumann algebra**: an isometry is a unitary.
The complement projection `1 − vv⋆` is a member with trace zero — by
traciality, its trace is `τ(1) − τ(v⋆v) = 0` — and a projection of zero
faithful trace vanishes. -/
theorem mul_star_eq_one_of_star_mul_eq_one
    {v : GroupHilbert G →L[ℂ] GroupHilbert G}
    (hv : v ∈ groupVonNeumannAlgebra G)
    (h : star v * v = 1) : v * star v = 1 := by
  have hvstar : star v ∈ groupVonNeumannAlgebra G := star_mem hv
  have hmem : v * star v ∈ groupVonNeumannAlgebra G := mul_mem hv hvstar
  have hPmem : 1 - v * star v ∈ groupVonNeumannAlgebra G :=
    sub_mem (one_mem _) hmem
  -- the trace of `v v⋆` is `1`
  have htrace : ((v * star v) (deltaOne G)) 1 = 1 := by
    have hcomm := coefficient_mul_comm G hv hvstar
    rw [hcomm, h]
    exact coefficient_one G
  -- `1 − v v⋆` is a self-adjoint idempotent
  have hsa : star (1 - v * star v) = 1 - v * star v := by
    rw [star_sub, star_one, star_mul, star_star]
  have hidem : (v * star v) * (v * star v) = v * star v := by
    calc (v * star v) * (v * star v)
        = v * (star v * v) * star v := by
          rw [mul_assoc, mul_assoc, ← mul_assoc (star v) v (star v),
            ← mul_assoc v (star v * v) (star v)]
      _ = v * star v := by rw [h, mul_one]
  have hPP : (1 - v * star v) * (1 - v * star v) = 1 - v * star v := by
    have hexp : (1 - v * star v) * (1 - v * star v)
        = 1 - v * star v - v * star v + (v * star v) * (v * star v) := by
      noncomm_ring
    rw [hexp, hidem]
    abel
  -- its trace vanishes
  have hPcoef : ((1 - v * star v) (deltaOne G)) 1 = 0 := by
    have hsub : ((1 - v * star v) (deltaOne G)) 1
        = ((1 : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)) 1
          - ((v * star v) (deltaOne G)) 1 := by
      rw [sub_apply, lp.coeFn_sub, Pi.sub_apply]
    rw [hsub, coefficient_one, htrace, sub_self]
  -- a projection of trace zero vanishes
  have hstarPP : ((star (1 - v * star v) * (1 - v * star v))
      (deltaOne G)) 1 = 0 := by
    rw [hsa, hPP]
    exact hPcoef
  have hPzero : (1 : GroupHilbert G →L[ℂ] GroupHilbert G) - v * star v = 0 :=
    eq_zero_of_mem_of_coefficient_star_mul_self_eq_zero G hPmem hstarPP
  exact (sub_eq_zero.mp hPzero).symm

end

end GroupVonNeumann
end GroupApproximation
