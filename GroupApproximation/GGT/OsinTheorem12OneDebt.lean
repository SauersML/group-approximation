import GroupApproximation.GGT.DGOCorollary612Unconditional
import GroupApproximation.GGT.OsinTheorem54Unconditional

/-!
# Osin's Theorem 1.2 reduced to DGO Theorem 6.8

Osin's Theorem 5.4 and DGO Corollary 6.12 are theorems of this development.
Consequently the implication `(AH₃) ⇒ (AH₁)` now has exactly one remaining
geometric input: DGO Theorem 6.8.
-/

namespace GroupApproximation
namespace GGT

universe u v

/-- Osin's Theorem 1.2 from its sole remaining DGO input. -/
theorem osinTheorem12_of_dgoTheorem68 (h68 : DGOTheorem68.{u, v}) :
    OsinTheorem12.{u, v} :=
  osinTheorem12_of_two h68 OsinEnlargement.osinTheorem54_unconditional

end GGT
end GroupApproximation
