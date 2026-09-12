import GroupApproximation.GGT.DGOCorollary612Threshold
import GroupApproximation.GGT.HullSCRelatorSeparation2ConeOff

/-!
# Selecting the deep last powers in Hull's cyclic products

In Hull's proof of `yi`, after the orientation-pure detecting family and its
cone-off have been fixed, the products are made loxodromic by choosing the last
power sufficiently deep in the relative metric.  This file performs that
choice for an arbitrary candidate family.

The input `hunbounded` is exactly the remaining fact about the chosen cyclic
subgroup: its nonzero powers escape every relative ball.  The output contains
the actual exponent of every candidate and proves loxodromy of every resulting
product.  Thus product loxodromy is not an independent selection hypothesis.
Pairwise non-commensurability is deliberately not asserted here: that is the
separate conclusion of DGO Lemma 4.21(b), not a consequence of the threshold
argument.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v w

variable {G : Type u} [Group G] {Λ : Type w}

/-- Simultaneously choose a deep nonzero power for every prescribed prefix.

Each prefix is represented by a relative word with no letter from the last
peripheral subgroup.  The threshold form of DGO Corollary 6.12 assigns a depth
to that prefix.  `hunbounded` then chooses a power beyond the depth.  Choice is
pointwise, so no finiteness assumption on the candidate type is needed. -/
theorem exists_deepLastPower_loxodromic_family
    (D : RelGenSet G Λ) (lam : Λ)
    (hsymm : ∀ y ∈ D.base, y⁻¹ ∈ D.base)
    (hhyp : ∃ δ : ℝ, IsHyperbolicSpace δ (Cayley D.alphabet))
    {ι : Type v} (stem : ι → G)
    (word : ι → List (RelLetter G Λ))
    (hletter : ∀ j c, c ∈ word j → D.IsLetter c)
    (hvalue : ∀ j, RelLetter.listVal (word j) = stem j)
    (hnoLast : ∀ j c, c ∈ word j → ¬ c.IsCompOf lam)
    (hstem : ∀ j, stem j ∉ D.fam lam)
    (a : G) (ha : a ∈ D.fam lam)
    (hunbounded : ∀ N : ℕ, ∃ m : ℤ,
      m ≠ 0 ∧ a ^ m ∉ D.relBall lam N) :
    ∃ multiplier : ι → ℤ,
      (∀ j, multiplier j ≠ 0) ∧
      ∀ j, IsLoxodromic (stem j * a ^ multiplier j)
        (Cayley.base D.alphabet) := by
  classical
  have hthreshold : ∀ j : ι, ∃ N : ℕ,
      ∀ h ∈ D.fam lam, h ∉ D.relBall lam N →
        IsLoxodromic (stem j * h) (Cayley.base D.alphabet) := by
    intro j
    exact exists_threshold_isLoxodromic_mul_of_symm D lam hsymm hhyp
      (hstem j) (word j) (hletter j) (hvalue j) (hnoLast j)
  choose depth hdepth using hthreshold
  have hpower : ∀ j : ι, ∃ m : ℤ,
      m ≠ 0 ∧ a ^ m ∉ D.relBall lam (depth j) :=
    fun j => hunbounded (depth j)
  choose multiplier hmultiplier hdeep using hpower
  refine ⟨multiplier, hmultiplier, ?_⟩
  intro j
  exact hdepth j (a ^ multiplier j) (Subgroup.zpow_mem _ ha _) (hdeep j)

/-- The cone-off form used in Hull's `yi`.

The relative base is the original Hull alphabet, hence symmetric; the family is
the elementary-closure family supplied by the detector.  This specialization
removes all bookkeeping about the relative generating set from the eventual
cyclic-product constructor. -/
theorem exists_deepLastPower_loxodromic_family_coneOff
    (A : Alphabet G) {k : ℕ} (E : Fin k → Subgroup G) (lam : Fin k)
    (hhyp : ∃ δ : ℝ,
      IsHyperbolicSpace δ (Cayley (coneOffFamily A E).alphabet))
    {ι : Type v} (stem : ι → G)
    (word : ι → List (RelLetter G (Fin k)))
    (hletter : ∀ j c, c ∈ word j → (coneOffFamily A E).IsLetter c)
    (hvalue : ∀ j, RelLetter.listVal (word j) = stem j)
    (hnoLast : ∀ j c, c ∈ word j → ¬ c.IsCompOf lam)
    (hstem : ∀ j, stem j ∉ E lam)
    (a : G) (ha : a ∈ E lam)
    (hunbounded : ∀ N : ℕ, ∃ m : ℤ,
      m ≠ 0 ∧ a ^ m ∉ (coneOffFamily A E).relBall lam N) :
    ∃ multiplier : ι → ℤ,
      (∀ j, multiplier j ≠ 0) ∧
      ∀ j, IsLoxodromic (stem j * a ^ multiplier j)
        (Cayley.base (coneOffFamily A E).alphabet) := by
  exact exists_deepLastPower_loxodromic_family
    (coneOffFamily A E) lam A.symmetricGenerating.inv_mem hhyp
      stem word hletter hvalue hnoLast hstem a ha hunbounded

end HullSC
end GroupApproximation
