import GroupApproximation.Analysis.ShulmanFillNormingBlockHom
import GroupApproximation.Analysis.ShulmanFillSymmetricDoubleFlip

/-!
# Limits in the block space, and the entries of the flip

Two ingredients of the `M₂` amplification of Shulman's `𝒟`.

The first is the transport of convergence: the block space is a `PiLp`, whose
topology is the product topology induced by `WithLp.ofLp`, so coordinatewise
convergence of a sequence of block vectors is convergence.  With
`hBlockOp_coord` that immediately gives convergence of block operators from
convergence of their entries, which is all that the `hone` clause of `𝒟` and
the `*`-strong convergence of the flip ever need.

The second is the entry formula for the flip `((0,1),(1,0))`: it is `1` off the
diagonal and `0` on it.  `Analysis/ShulmanFillSymmetricDoubleFlip` proves the
identities the flip is used for, but never its entries, because the corona
argument there never had to push it through a homomorphism.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

open scoped InnerProductSpace

noncomputable section

section BlockLimit

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E] {n : ℕ}

omit [CompleteSpace E] in
/-- **Coordinatewise convergence is convergence in the block space.**  The
`PiLp` topology is `Pi.topologicalSpace.induced ofLp`, and `WithLp.toLp` is
continuous for it. -/
theorem tendsto_blockSpace_of_coord {f : ℕ → BlockSpace E n} {v : BlockSpace E n}
    (h : ∀ i : Fin n, Tendsto (fun m ↦ f m i) atTop (𝓝 (v i))) :
    Tendsto f atTop (𝓝 v) := by
  have hpi : Tendsto (fun m ↦ WithLp.ofLp (f m)) atTop (𝓝 (WithLp.ofLp v)) :=
    tendsto_pi_nhds.mpr h
  have hcont := (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ E)).tendsto
    (WithLp.ofLp v)
  have hcomp := hcont.comp hpi
  simp only [Function.comp_def, WithLp.toLp_ofLp] at hcomp
  exact hcomp

/-- **Entrywise convergence of block operators is strong convergence.**  Each
coordinate of `hBlockOp X w` is a finite sum of entries applied to coordinates
of `w`, so it converges as soon as every entry does. -/
theorem tendsto_hBlockOp_of_coord
    {Xm : ℕ → CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E)}
    {X : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E)}
    (h : ∀ (i j : Fin n) (x : E),
      Tendsto (fun m ↦ (Xm m i j) x) atTop (𝓝 ((X i j) x)))
    (w : BlockSpace E n) :
    Tendsto (fun m ↦ hBlockOp (Xm m) w) atTop (𝓝 (hBlockOp X w)) := by
  refine tendsto_blockSpace_of_coord fun i ↦ ?_
  have hcoord : ∀ m : ℕ, hBlockOp (Xm m) w i = ∑ j : Fin n, (Xm m i j) (w j) :=
    fun m ↦ hBlockOp_coord (Xm m) w i
  rw [funext hcoord, hBlockOp_coord]
  exact tendsto_finsetSum _ fun j _ ↦ h i j (w j)

end BlockLimit

/-! ## The entries of the flip -/

section FlipEntries

variable {D : Type} [CStarAlgebra D]

/-- The flip is `1` off the diagonal and `0` on it. -/
theorem flip2_apply_ne {i j : Fin 2} (h : i ≠ j) :
    (flip2 : CStarMatrix (Fin 2) (Fin 2) D) i j = 1 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [flip2, cStarMatrixUnit2, CStarMatrix.add_apply]

theorem flip2_apply_self (i : Fin 2) :
    (flip2 : CStarMatrix (Fin 2) (Fin 2) D) i i = 0 := by
  fin_cases i <;>
    simp [flip2, cStarMatrixUnit2, CStarMatrix.add_apply]

end FlipEntries

end

end ShulmanFill
end GroupApproximation
