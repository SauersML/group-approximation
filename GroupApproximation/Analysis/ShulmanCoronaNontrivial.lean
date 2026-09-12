import GroupApproximation.Analysis.CStarProductCorona

/-!
# Nontriviality of a C-star product corona

For a nontrivial filter, the constant unit sequence is not null.  Its class
therefore witnesses that the product corona is nontrivial.  This is the
minimal extra hypothesis needed to use the nonunital continuous functional
calculus on the quotient: for the bottom filter the null ideal is the whole
bounded product, so the quotient really is trivial.
-/

namespace GroupApproximation
namespace ShulmanCoronaNontrivial

open Filter PolarLiftingGeneralCStar

noncomputable section

universe u

variable (A : ℕ → Type u) [∀ n, CStarAlgebra (A n)]
  [∀ n, Nontrivial (A n)] (l : Filter ℕ) [l.NeBot]

/-- The class of the constant unit sequence is nonzero when the defining
filter is nontrivial. -/
theorem quotient_one_ne_zero :
    cStarProductCoronaQuotient A l (1 : BoundedCStarSequence A) ≠ 0 := by
  intro hzero
  have hnull : IsNullCStarSequence A l (1 : BoundedCStarSequence A) :=
    (cStarProductCoronaQuotient_eq_zero_iff A l _).1 hzero
  have hone : Tendsto
      (fun n ↦ ‖(1 : BoundedCStarSequence A) n‖) l (nhds 1) := by
    simp
  have : (1 : ℝ) = 0 := tendsto_nhds_unique hone hnull
  norm_num at this

/-- A reduced product over a nontrivial filter is nontrivial. -/
noncomputable instance cStarProductCoronaNontrivial :
    Nontrivial (CStarProductCorona A l) :=
  ⟨⟨cStarProductCoronaQuotient A l (1 : BoundedCStarSequence A), 0,
    quotient_one_ne_zero A l⟩⟩

end

end ShulmanCoronaNontrivial
end GroupApproximation
