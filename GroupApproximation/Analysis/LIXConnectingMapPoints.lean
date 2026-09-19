import GroupApproximation.Analysis.LIXBlockProjections
import Mathlib.Topology.Bases
import Mathlib.Data.Nat.Pairing

set_option autoImplicit false

/-!
# The dense point sequence of the STW LIX tower

The manuscript's §4 chooses points `x_i ∈ X_i` such that for every `k` the tail
`{π_{k,i}(x_i) : i ≥ k}` is dense in `X_k`, by listing a countable dense subset of the
compact metrizable product

  `X_∞ = S⁴ × ∏_{j} ℂP^{r_j}`   (`STW59.baseXinf`)

with every point repeated infinitely often and projecting the `i`-th member to `X_i`.
This file carries that out.  The repetition is the Cantor pairing: the `i`-th point is
the `(Nat.unpair i).2`-th member of the chosen dense sequence, truncated to `X_i`, and
for fixed `k` the indices `i = ⟨k, n⟩` are all `≥ k`, so every member of the dense
sequence is hit by the tail beyond `k`.

Everything is stated through `STW59.truncate`, the projection `X_∞ → X_i`, so that no
equality of the form `(Nat.unpair (Nat.pair k n)).1 = k` ever has to be transported
across a dependent type: it occurs only in the *index* of a dense sequence living on the
fixed space `X_∞`.

## Main results

* `STW59.stagePoint i : baseX i` — the manuscript's `x_i`.
* `STW59.exists_stagePoint_mem_of_isOpen` — for every `k` and every nonempty open
  `U ⊆ X_k` there is `i ≥ k` with `π_{k,i}(x_i) ∈ U`.  This is the form the simplicity
  argument consumes.
* `STW59.dense_stagePoint_tail` — the same statement as density of the tail.
-/

namespace GroupApproximation
namespace STW59

open scoped Matrix

noncomputable section

/-! ### Separability of the base spaces -/

instance instSecondCountableMatrix (m n : Type*) [Countable m] [Countable n] :
    SecondCountableTopology (Matrix m n ℂ) :=
  inferInstanceAs (SecondCountableTopology (m → n → ℂ))

instance CP.instSecondCountableTopology (d : ℕ) : SecondCountableTopology (CP d) :=
  inferInstanceAs (SecondCountableTopology ↥(cpSet d))

instance sphereFour.instSecondCountableTopology :
    SecondCountableTopology ↥sphereFour :=
  inferInstanceAs (SecondCountableTopology ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1))

/-! ### `X_∞` and the truncations -/

/-- `X_∞ = S⁴ × ∏_j ℂP^{r_j}`, the space whose countable dense subset the manuscript
lists. -/
abbrev baseXinf : Type := ↥sphereFour × (∀ j : ℕ, CP (stageRank j))

instance baseXinf.instNonempty : Nonempty baseXinf := inferInstance

instance baseXinf.instSeparableSpace : TopologicalSpace.SeparableSpace baseXinf :=
  inferInstance

/-- The truncation `X_∞ → X_i`. -/
def truncate (i : ℕ) : C(baseXinf, baseX i) :=
  ⟨fun w => (w.1, fun j => w.2 (j : ℕ)), by
    refine Continuous.prodMk continuous_fst (continuous_pi fun j => ?_)
    exact (continuous_apply ((j : ℕ))).comp continuous_snd⟩

@[simp]
theorem truncate_apply (i : ℕ) (w : baseXinf) :
    truncate i w = (w.1, fun j : Fin i => w.2 (j : ℕ)) := rfl

/-- Truncation is compatible with the coordinate projections of the tower. -/
theorem basePr_truncate {k i : ℕ} (h : k ≤ i) (w : baseXinf) :
    basePr h (truncate i w) = truncate k w := rfl

theorem truncate_surjective (i : ℕ) : Function.Surjective (truncate i) := by
  classical
  rintro ⟨y1, y2⟩
  refine ⟨⟨y1, fun j : ℕ => if hj : j < i then y2 ⟨j, hj⟩ else Classical.arbitrary _⟩, ?_⟩
  exact Prod.ext rfl (funext fun j => dif_pos j.2)

/-! ### The points `x_i` -/

/-- A dense sequence in `X_∞`. -/
def infDenseSeq : ℕ → baseXinf := TopologicalSpace.denseSeq baseXinf

theorem denseRange_infDenseSeq : DenseRange infDenseSeq :=
  TopologicalSpace.denseRange_denseSeq baseXinf

/-- **The manuscript's `x_i`**: the `(Nat.unpair i).2`-th member of a fixed dense
sequence of `X_∞`, truncated to `X_i`. -/
def stagePoint (i : ℕ) : baseX i := truncate i (infDenseSeq (Nat.unpair i).2)

theorem stagePoint_def (i : ℕ) :
    stagePoint i = truncate i (infDenseSeq (Nat.unpair i).2) := rfl

/-- **Every tail of `{π_{k,i}(x_i)}` meets every nonempty open set of `X_k`.** -/
theorem exists_stagePoint_mem_of_isOpen {k : ℕ} {U : Set (baseX k)} (hU : IsOpen U)
    (hne : U.Nonempty) : ∃ (i : ℕ) (h : k ≤ i), basePr h (stagePoint i) ∈ U := by
  have hopen : IsOpen ((truncate k) ⁻¹' U) := hU.preimage (truncate k).continuous
  obtain ⟨y, hy⟩ := hne
  obtain ⟨w, hw⟩ := truncate_surjective k y
  have hne' : ((truncate k) ⁻¹' U).Nonempty := ⟨w, by
    rw [Set.mem_preimage, hw]
    exact hy⟩
  obtain ⟨n, hn⟩ := denseRange_infDenseSeq.exists_mem_open hopen hne'
  refine ⟨Nat.pair k n, Nat.left_le_pair k n, ?_⟩
  rw [stagePoint_def, Nat.unpair_pair, basePr_truncate]
  exact hn

/-- **The manuscript's density statement**: for every `k`, the tail
`{π_{k,i}(x_i) : i ≥ k}` is dense in `X_k`. -/
theorem dense_stagePoint_tail (k : ℕ) :
    Dense {y : baseX k | ∃ (i : ℕ) (h : k ≤ i), basePr h (stagePoint i) = y} := by
  rw [dense_iff_inter_open]
  intro U hU hne
  obtain ⟨i, h, hmem⟩ := exists_stagePoint_mem_of_isOpen hU hne
  exact ⟨basePr h (stagePoint i), hmem, ⟨i, h, rfl⟩⟩

end

end STW59
end GroupApproximation
