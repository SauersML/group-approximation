import NonsoficGroupsExist.Kazhdan.DiagonalInvariantRelation
import NonsoficGroupsExist.Matching.PartialSwapEquivariance

/-!
# Exact Kazhdan repair for finite partial intertwiners

A partial bijection between two finite `G`-sets is encoded by its swap
involution on their disjoint union.  The two actions combine to an exact
action on that union.  Applying diagonal Kazhdan repair to the swap and then
extracting its left-to-right crossings produces a repaired partial
bijection.  This file gives the explicit two-sided distance estimate needed
by the finite cluster-composition interface.
-/

namespace NonsoficGroupsExist
namespace ExactPartialKazhdanRepair

open DiagonalInvariantRelation
open FinitePartialBijection

universe u

variable {G : Type u} [Group G]
variable {Y Z : FiniteModel}

/-- Componentwise exact action on a disjoint union. -/
def sumActionHom (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z) :
    G →* Equiv.Perm (sumModel Y Z) where
  toFun g := sumAction σY σZ g
  map_one' := by
    ext x
    cases x <;> simp [sumAction]
  map_mul' g h := by
    ext x
    cases x <;> simp [sumAction]

@[simp] theorem sumActionHom_apply
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (g : G) (x : Y ⊕ Z) :
    sumActionHom σY σZ g x = Sum.map (σY g) (σZ g) x := by
  cases x <;> rfl

/-- Repair the swap permutation and extract its crossing partial map. -/
noncomputable def repair
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z) : FinitePartialBijection Y Z :=
  extractCrossing
    (roundedDiagonalPermutation (sumActionHom σY σZ) b.swapPerm)

/-- The repaired arrow is close to the original partial arrow.  The intrinsic
missing source and target masses are retained explicitly; every additional
disagreement is controlled by the Kazhdan repair of the swap permutation. -/
theorem kazhdan_mul_twoSidedDisagreement_repair_le
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, 0} G Q ε)
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z) :
    ε ^ 2 * (b.twoSidedDisagreement (repair σY σZ b) : ℝ) ≤
      ε ^ 2 * (b.sourceDefect + b.targetDefect : ℕ) +
        16 * (totalCommutationDefect
          (sumActionHom σY σZ) Q b.swapPerm : ℝ) := by
  let p := roundedDiagonalPermutation (sumActionHom σY σZ) b.swapPerm
  have htwoNat :=
    twoSidedDisagreement_extractCrossing_le_self_add_two_mul b p
  have htwo : (b.twoSidedDisagreement (extractCrossing p) : ℝ) ≤
      (b.sourceDefect + b.targetDefect : ℕ) +
        2 * ((hammingDisagreement b.swapPerm p).card : ℕ) := by
    exact_mod_cast htwoNat
  have hsymm :
      hammingDisagreement b.swapPerm p =
        hammingDisagreement p b.swapPerm := by
    ext x
    simp [hammingDisagreement, ne_comm]
  have hham :=
    kazhdan_mul_card_hammingDisagreement_roundedDiagonalPermutation_le
      hQ (sumActionHom σY σZ) b.swapPerm
  rw [← hsymm] at hham
  have hscaled := mul_le_mul_of_nonneg_left htwo (sq_nonneg ε)
  change ε ^ 2 * (b.twoSidedDisagreement (extractCrossing p) : ℝ) ≤ _
  nlinarith

/-- The repaired swap itself has quantitatively controlled commutation
defect for the finite image of `Q`. -/
theorem kazhdan_mul_card_badArcs_repairedSwap_le
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, 0} G Q ε)
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z) :
    ε ^ 2 *
        ((AlmostAutomorphism.badArcs (sumModel Y Z)
          (Q.image (sumActionHom σY σZ))
          (roundedDiagonalPermutation
            (sumActionHom σY σZ) b.swapPerm)).card : ℝ) ≤
      8 * (Q.card : ℝ) *
        (totalCommutationDefect
          (sumActionHom σY σZ) Q b.swapPerm : ℝ) :=
  kazhdan_mul_card_badArcs_roundedDiagonalPermutation_le
    hQ (sumActionHom σY σZ) b.swapPerm

end ExactPartialKazhdanRepair
end NonsoficGroupsExist
