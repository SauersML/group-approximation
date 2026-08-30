import GroupApproximation.GGT.ElementaryCoarseTranslationProper
import GroupApproximation.GGT.HullSCConeOffHeavyUnconditional

/-!
# Coarse translation as a Cayley word-metric bound

The uniform axis statement immediately puts the elementary closure in a
uniform neighborhood of the cyclic subgroup.  This is the Hausdorff-distance
input used by the cone-off hyperbolicity argument.
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

variable {G : Type u} [Group G]

/-- Every element of `E(h)` is uniformly close to a power of `h` in the Cayley
metric, as a direct specialization of uniform coarse translation at `m = 0`. -/
theorem exists_wordDist_zpowers_le_of_coarseTranslation (A : Alphabet G)
    {h : G} (hlox : IsLoxodromic h (Cayley.base A))
    (hct : ElementaryClosureCoarseTranslation G (Cayley.base A)) :
    ∃ D : ℕ, ∀ b ∈ elementaryClosure h,
      ∃ b' ∈ Subgroup.zpowers h, wordDist A.carrier b b' ≤ D := by
  obtain ⟨K, _hK, hnear⟩ := hct h hlox
  refine ⟨⌈K⌉₊, ?_⟩
  intro b hb
  obtain ⟨e, c, _he, hbc⟩ := hnear b hb
  have hd := hbc 0
  simp only [zpow_zero, mul_one] at hd
  rw [Cayley.dist_eq, Cayley.val_smul, Cayley.val_smul, Cayley.val_base,
    mul_one] at hd
  have hd' : ((wordDist A.carrier b (h ^ c) : ℕ) : ℝ) ≤ K := by
    simpa only [mul_zero, zero_add, mul_one] using hd
  refine ⟨h ^ c, Subgroup.mem_zpowers_iff.mpr ⟨c, rfl⟩, ?_⟩
  exact_mod_cast hd'.trans (Nat.le_ceil K)

end Elementary
end GGT
end GroupApproximation
