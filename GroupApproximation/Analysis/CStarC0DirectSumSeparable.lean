import GroupApproximation.Analysis.CStarC0DirectSum
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Separability of countable C-star `c₀`-sums

The finite truncations of a norm-null sequence are dense.  If every coordinate
algebra is separable, each finite truncation space has a countable dense
sequence; taking the union of those sequences over the truncation length gives
one countable dense set in the whole `c₀`-sum.

The final theorem passes separability to the minimal unitization through the
continuous surjection `(c, a) ↦ c + a`.
-/

namespace GroupApproximation
namespace CStarC0DirectSum

open Filter Topology PolarLiftingGeneralCStar

noncomputable section

set_option linter.unusedSectionVars false

universe u

variable (D : ℕ → Type u) [∀ n, CStarAlgebra (D n)]
  [∀ n, Nontrivial (D n)] [∀ n, TopologicalSpace.SeparableSpace (D n)]

/-- Assemble the first `N` coordinates of a dependent finite tuple. -/
def finiteAssembly (N : ℕ) (x : ∀ n : Fin N, D n.1) : C0DirectSum D :=
  ∑ n : Fin N, summandInclusion D n.1 (x n)

private theorem continuous_summandInclusion (n : ℕ) :
    Continuous (summandInclusion D n) := by
  exact (LipschitzWith.of_dist_le_mul (K := 1) fun x y ↦ by
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← map_sub]
    exact NonUnitalStarAlgHom.norm_apply_le (summandInclusion D n) (x - y)).continuous

private theorem continuous_finiteAssembly (N : ℕ) :
    Continuous (finiteAssembly D N) := by
  classical
  unfold finiteAssembly
  exact continuous_finsetSum Finset.univ fun n _ ↦
    (continuous_summandInclusion D n.1).comp (continuous_apply n)

/-- The countable set obtained by taking a dense sequence in every finite
coordinate product. -/
def finiteDenseSet : Set (C0DirectSum D) :=
  ⋃ N : ℕ, Set.range fun k : ℕ ↦
    finiteAssembly D N
      (TopologicalSpace.denseSeq (∀ n : Fin N, D n.1) k)

theorem finiteDenseSet_countable : (finiteDenseSet D).Countable := by
  apply Set.countable_iUnion
  intro N
  exact Set.countable_range _

private theorem truncation_eq_finiteAssembly (b : C0DirectSum D) (N : ℕ) :
    truncation D b N = finiteAssembly D N (fun n ↦ b.1 n.1) := by
  classical
  rw [truncation, finiteAssembly]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n hn
  simp [Finset.mem_range.mp hn]

private theorem finiteAssembly_mem_closure_finiteDenseSet (N : ℕ)
    (x : ∀ n : Fin N, D n.1) :
    finiteAssembly D N x ∈ closure (finiteDenseSet D) := by
  let dense : ℕ → (∀ n : Fin N, D n.1) :=
    TopologicalSpace.denseSeq (∀ n : Fin N, D n.1)
  have hx : x ∈ closure (Set.range dense) :=
    TopologicalSpace.denseRange_denseSeq _ x
  have himage : finiteAssembly D N x ∈
      closure (finiteAssembly D N '' Set.range dense) :=
    image_closure_subset_closure_image (continuous_finiteAssembly D N)
      ⟨x, hx, rfl⟩
  apply closure_mono _ himage
  rintro y ⟨z, ⟨k, rfl⟩, rfl⟩
  exact Set.mem_iUnion.2 ⟨N, ⟨k, rfl⟩⟩

theorem dense_finiteDenseSet : Dense (finiteDenseSet D) := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro b
  apply isClosed_closure.mem_of_tendsto (tendsto_truncation D b)
  exact Eventually.of_forall fun N ↦ by
    rw [truncation_eq_finiteAssembly]
    exact finiteAssembly_mem_closure_finiteDenseSet D N _

/-- A countable `c₀`-sum of separable C-star algebras is separable. -/
theorem separableSpace_c0DirectSum :
    TopologicalSpace.SeparableSpace (C0DirectSum D) := by
  let t := finiteDenseSet D
  letI : Countable t := (finiteDenseSet_countable D).to_subtype
  exact TopologicalSpace.SeparableSpace.of_denseRange
    (fun x : t ↦ (x.1 : C0DirectSum D)) (by
      simpa [t, DenseRange] using dense_finiteDenseSet D)

/-- The minimal unitization of a separable nonunital C-star algebra is
separable. -/
theorem separableSpace_unitization_c0DirectSum :
    TopologicalSpace.SeparableSpace (Unitization ℂ (C0DirectSum D)) := by
  letI : TopologicalSpace.SeparableSpace (C0DirectSum D) :=
    separableSpace_c0DirectSum D
  let assemble : ℂ × C0DirectSum D → Unitization ℂ (C0DirectSum D) :=
    fun x ↦ Unitization.inl x.1 + (x.2 : Unitization ℂ (C0DirectSum D))
  have hcontinuous : Continuous assemble := by
    have halg : Continuous
        (algebraMap ℂ (Unitization ℂ (C0DirectSum D))) :=
      (LipschitzWith.of_dist_le_mul (K := 1) fun c d ↦ by
        rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
        change
          ‖algebraMap ℂ (Unitization ℂ (C0DirectSum D)) c -
              algebraMap ℂ (Unitization ℂ (C0DirectSum D)) d‖ ≤ ‖c - d‖
        rw [← map_sub (algebraMap ℂ (Unitization ℂ (C0DirectSum D))) c d,
          norm_algebraMap']).continuous
    have hinl : Continuous
        (Unitization.inl : ℂ → Unitization ℂ (C0DirectSum D)) := by
      simpa only [Unitization.algebraMap_eq_inl] using halg
    exact (hinl.comp continuous_fst).add
      (Unitization.continuous_inr.comp continuous_snd)
  have hsurjective : Function.Surjective assemble := by
    intro x
    exact ⟨(x.fst, x.snd), Unitization.inl_fst_add_inr_snd_eq x⟩
  exact hsurjective.denseRange.separableSpace hcontinuous

end

end CStarC0DirectSum
end GroupApproximation
