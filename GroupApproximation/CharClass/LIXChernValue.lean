import GroupApproximation.CharClass.LIXChern
import GroupApproximation.CharClass.LIXBundleModel
import GroupApproximation.CharClass.LIXBaseInstances

/-!
# The Chern classes on a family of constant positive rank

`lixChern` is total, so it branches classically on whether the bundle has constant
positive rank; a consumer that needs the value rather than the class has to know the
branch is taken.  This is that lemma, in the same shape as `lixChernOf_mappingTorus`,
and its instance at the mapping torus.

The transport across the two spellings of the rank is free for a reason worth naming.
`LerayHirschGraded` is a `Prop` and the only data in `LerayHirschData` is the
projection, the rank and the class, so once the chosen rank is identified with the
given one the two data agree by structure eta and proof irrelevance.  Had the
Leray–Hirsch statement been data-valued this step would have needed a real transport.

## Main declarations

* `chern_congr_rank` — the datum does not depend on which spelling of the rank.
* `lixChern_eq_of_rank` — **the branch is taken**, at any constant positive rank.
* `lixChern_mappingTorus` — its instance on a mapping torus.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace CharClass

open CategoryTheory
open GroupApproximation.STW59

noncomputable section

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-- The Leray–Hirsch datum does not depend on which spelling of the rank it was
built from. -/
theorem chern_congr_rank {X : Type} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    {ι : Type} [Fintype ι] [DecidableEq ι] (q : Bundle X ι) {s t : ℕ} (h : s = t)
    (hs : ∀ x, q.rank x = s) (hs1 : 1 ≤ s) (ht : ∀ x, q.rank x = t) (ht1 : 1 ≤ t)
    (k : ℕ) :
    (LHCast.lerayHirschData_of_graded (LH.lerayHirschGraded_compact q s hs hs1)).chern k
      = (LHCast.lerayHirschData_of_graded (LH.lerayHirschGraded_compact q t ht ht1)).chern k := by
  subst h
  rfl

open scoped Classical in
/-- **The branch is taken** whenever the bundle has constant positive rank. -/
theorem lixChern_eq_of_rank (P : LixFamily dd) (hcont : Continuous P)
    (hproj : ∀ p, IsStarProjection (P p)) (s : ℕ) (hs1 : 1 ≤ s)
    (hs : ∀ x, (⟨P, hcont, hproj⟩ : Bundle _ _).rank x = s) (k : ℕ) :
    lixChern dd P hcont hproj k
      = TotalH.component (lixN dd) (2 * k)
          ((LHCast.lerayHirschData_of_graded
            (LH.lerayHirschGraded_compact (⟨P, hcont, hproj⟩ : Bundle _ _) s hs hs1)).chern
              k) := by
  have hex : ∃ s : ℕ, 1 ≤ s ∧ ∀ x, (⟨P, hcont, hproj⟩ : Bundle _ _).rank x = s :=
    ⟨s, hs1, hs⟩
  have hchoose : hex.choose = s := by
    obtain ⟨x⟩ := (inferInstance : Nonempty (↥sphereOne × baseM dd))
    exact (hex.choose_spec.2 x).symm.trans (hs x)
  show dite _ _ _ = _
  rw [dif_pos hex]
  exact congrArg _ (chern_congr_rank _ hchoose
    hex.choose_spec.2 hex.choose_spec.1 hs hs1 k)

/-- **The branch is taken on a mapping torus**, at the rank `cc-lix-odd` computes. -/
theorem lixChern_mappingTorus (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ)
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hcont : Continuous (mappingTorus Vmat G circHoriz circHeight))
    (hproj : ∀ p, IsStarProjection (mappingTorus Vmat G circHoriz circHeight p))
    (k : ℕ) :
    lixChern dd (mappingTorus Vmat G circHoriz circHeight) hcont hproj k
      = TotalH.component (lixN dd) (2 * k)
          ((LHCast.lerayHirschData_of_graded
            (LH.lerayHirschGraded_compact
              (⟨mappingTorus Vmat G circHoriz circHeight, hcont, hproj⟩ : Bundle _ _)
              (lixRank dd) (fun x => rank_lixBundle G hGc hGu x)
              (by simp [lixRank]))).chern k) :=
  lixChern_eq_of_rank _ hcont hproj (lixRank dd) (by simp [lixRank])
    (fun x => rank_lixBundle G hGc hGu x) k

end

end CharClass
end GroupApproximation
