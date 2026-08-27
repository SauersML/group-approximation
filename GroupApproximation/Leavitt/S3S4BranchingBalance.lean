import Mathlib.Tactic

/-!
# The regular `S₄ -> S₃` branching vector is Hall-balanced

The raw atlas cell localizes to `S₃`, and each hard class-11 extension has
classical value `S₄`.  This file records the exact complex branching matrix
and verifies its load-bearing limitation: the regular `S₄` multiplicity
vector restricts to four copies of the regular `S₃` vector.  Consequently
ordinary representation-type counts cannot produce a Hall deficit.
-/

namespace GroupApproximation
namespace S3S4BranchingBalance

/-- Rows are `1, sign, 2, 3, 3*sign`; columns are `1, sign, standard₂`. -/
def restrictionMultiplicity : Fin 5 → Fin 3 → ℕ
  | 0, 0 => 1
  | 1, 1 => 1
  | 2, 2 => 1
  | 3, 0 => 1
  | 3, 2 => 1
  | 4, 1 => 1
  | 4, 2 => 1
  | _, _ => 0

/-- Irreducible multiplicities in the regular representation of `S₄`. -/
def s4RegularMultiplicity : Fin 5 → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3

/-- Irreducible multiplicities in the regular representation of `S₃`. -/
def s3RegularMultiplicity : Fin 3 → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2

/-- The regular dimension vector is exactly balanced across the hard edge:
`Res^{S₄}_{S₃}(lambda_{S₄}) = 4 lambda_{S₃}`. -/
theorem regular_restriction_balanced :
    ∀ j : Fin 3,
      (∑ i : Fin 5,
        s4RegularMultiplicity i * restrictionMultiplicity i j) =
          4 * s3RegularMultiplicity j := by
  decide

end S3S4BranchingBalance
end GroupApproximation
