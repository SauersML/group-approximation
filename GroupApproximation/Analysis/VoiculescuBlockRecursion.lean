import GroupApproximation.Analysis.VoiculescuBlockCompact

/-!
# (V4) The recursion: isometries with pairwise orthogonal ranges

The assembly runs the intertwining step once per block, and needs the resulting
isometries to have pairwise orthogonal ranges.  That is arranged by feeding each
step the span of the previous ranges as its obstruction subspace, which is
finite-dimensional because the blocks are.  This module is that recursion, and
nothing else: it mentions no representation, no defect and no tolerance.

## The shape of the induction

The step is available at every finite-dimensional obstruction, so the recursion
carries the accumulated span *together with its finite-dimensionality* — a
subtype-valued `Nat.rec`, since the choice at stage `m` cannot be made until the
stage `m-1` subspace exists, and the step will not fire without the proof.  The
per-stage property is abstracted as `Q`, so that the tolerance bookkeeping stays
with the caller.

## Why the orthogonality comes out

Each stage lands in the orthogonal complement of everything accumulated so far,
and the accumulation is monotone, so for `k < m` the range of `V k` sits inside
the obstruction that `V m` avoids.  The other order is conjugate symmetry of the
inner product, not a second argument — which is why the conclusion is stated
symmetrically in `m` and `n` rather than for `m < n`.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped InnerProductSpace

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
  {G : ℕ → Type} [∀ m, NormedAddCommGroup (G m)] [∀ m, InnerProductSpace ℂ (G m)]
  [∀ m, FiniteDimensional ℂ (G m)] [∀ m, CompleteSpace (G m)]

/-- **The recursion.**  A one-step construction available at every
finite-dimensional obstruction yields a whole sequence of isometries with
pairwise orthogonal ranges, each still satisfying the step's own property. -/
theorem exists_seq_orthogonal_ranges (Q : ∀ m, (G m →L[ℂ] H) → Prop)
    (step : ∀ (m : ℕ) (P : Submodule ℂ H), FiniteDimensional ℂ ↥P →
      ∃ V : G m →L[ℂ] H, ContinuousLinearMap.adjoint V ∘L V = 1 ∧
        (∀ x, V x ∈ Pᗮ) ∧ Q m V) :
    ∃ V : ∀ m, G m →L[ℂ] H,
      (∀ m, ContinuousLinearMap.adjoint (V m) ∘L V m = 1) ∧
      (∀ m, Q m (V m)) ∧
      (∀ m n, m ≠ n → ∀ (x : G m) (y : G n), ⟪V m x, V n y⟫_ℂ = 0) := by
  classical
  choose Vch hiso hperp hQ using step
  -- the accumulated span, carrying its finite-dimensionality
  set Acc : ℕ → { P : Submodule ℂ H // FiniteDimensional ℂ ↥P } := fun m ↦
    Nat.rec (motive := fun _ ↦ { P : Submodule ℂ H // FiniteDimensional ℂ ↥P })
      ⟨⊥, inferInstance⟩
      (fun k acc ↦
        ⟨acc.1 ⊔ LinearMap.range (Vch k acc.1 acc.2).toLinearMap, by
          haveI := acc.2
          infer_instance⟩)
      m with hAccDef
  set V : ∀ m, G m →L[ℂ] H := fun m ↦ Vch m (Acc m).1 (Acc m).2 with hVdef
  have hAccSucc : ∀ m, (Acc (m + 1)).1
      = (Acc m).1 ⊔ LinearMap.range (V m).toLinearMap := fun _ ↦ rfl
  have hmono : Monotone fun m ↦ (Acc m).1 := by
    refine monotone_nat_of_le_succ fun m ↦ ?_
    rw [hAccSucc m]
    exact le_sup_left
  have hrange : ∀ m, LinearMap.range (V m).toLinearMap ≤ (Acc (m + 1)).1 := by
    intro m
    rw [hAccSucc m]
    exact le_sup_right
  have hmem : ∀ m n, m < n → ∀ x : G m, V m x ∈ (Acc n).1 := by
    intro m n hmn x
    exact hmono hmn (hrange m ⟨x, rfl⟩)
  have horthLt : ∀ m n, m < n → ∀ (x : G m) (y : G n), ⟪V m x, V n y⟫_ℂ = 0 := by
    intro m n hmn x y
    exact (Submodule.mem_orthogonal _ _).mp (hperp n (Acc n).1 (Acc n).2 y) _
      (hmem m n hmn x)
  refine ⟨V, fun m ↦ hiso m (Acc m).1 (Acc m).2,
    fun m ↦ hQ m (Acc m).1 (Acc m).2, ?_⟩
  intro m n hmn x y
  rcases lt_or_gt_of_ne hmn with h | h
  · exact horthLt m n h x y
  · have h2 : ⟪V n y, V m x⟫_ℂ = 0 := horthLt n m h y x
    have h3 := congrArg (starRingEnd ℂ) h2
    rw [inner_conj_symm, map_zero] at h3
    exact h3

end

end ShulmanFill
end GroupApproximation
