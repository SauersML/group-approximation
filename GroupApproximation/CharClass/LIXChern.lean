import GroupApproximation.CharClass.LerayHirschCompact
import GroupApproximation.CharClass.CohomologyLHRingData
import GroupApproximation.CharClass.LemmaTwoTopClass

/-!
# The degreewise mod-2 Chern classes on the mapping-torus base

`LixChernDeg` quantifies over *every* family on the base, including ones whose bundle
has rank zero, so the assignment has to be total in the same way `lixChernOf` is.  It
branches classically on whether the bundle has constant positive rank; on that branch
it is the degree-`2k` component of the `k`-th Chern class, reached through the
compact-base Leray–Hirsch instance and `cc-cohom-api`'s ring-level constructor.

Adding the rank as a hypothesis instead would have been worse than it looks:
`LixChernDeg` is an `abbrev`, so the hypothesis would unfold into every consumer's
binder rather than staying here.  `cc-lix-odd` made that point and it decided the
design.

The base's circle factor carries neither `CompactSpace` nor `Nonempty` as an
instance, so both are introduced locally rather than registered: they belong with the
base, and a consumer that registers them globally is how a second spelling starts.
The other factor already has both, as `sphereFive`.

The branch is taken on a mapping torus, by `rank_lixBundle`; that is a separate
lemma, in the same shape as `lixChernOf_mappingTorus`, so nothing about the branch
reaches a consumer.

## Main declarations

* `lixChern` — **the degreewise Chern classes**, total.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace CharClass

open CategoryTheory
open GroupApproximation.STW59

noncomputable section

variable {ℓ : ℕ}

open scoped Classical in
/-- **The degreewise mod-2 Chern classes** of a projection-valued family on the
mapping-torus base.  Total: zero off the families of constant positive rank. -/
def lixChern (dd : Fin ℓ → ℕ) : LixChernDeg dd :=
  fun P hcont hproj k =>
    haveI : CompactSpace ↥sphereOne :=
      isCompact_iff_compactSpace.mp (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)
    haveI : Nonempty ↥sphereOne :=
      (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype
    if h : ∃ s : ℕ, 1 ≤ s ∧ ∀ x, (⟨P, hcont, hproj⟩ : Bundle _ _).rank x = s then
      TotalH.component (lixN dd) (2 * k)
        ((LHCast.lerayHirschData_of_graded
          (LH.lerayHirschGraded_compact (⟨P, hcont, hproj⟩ : Bundle _ _)
            h.choose h.choose_spec.2 h.choose_spec.1)).chern k)
    else 0

end

end CharClass
end GroupApproximation
