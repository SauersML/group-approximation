import GroupApproximation.CharClass.LerayHirschChartTautGen
import GroupApproximation.CharClass.BundleRankCard

/-!
# Leray–Hirsch for a projectivised bundle over a compact base

The endpoint of the ring side.  Every input is now green: the general-rank ladder,
the chart transport, the class identification at an arbitrary isomorphism,
`cc-bundle`'s trivialisation over a subset of a trivialising set and their chart
identification of the tautological line, and the rank-one branch where no chart step
exists at all.

The proof splits on the rank and only on the rank.  At rank one the fibre is a point
and the projection is a homeomorphism.  Above it the cover induction runs over the
trivialising sets, and each chart step is the ladder read through the trivialisation.

Stated for an arbitrary bundle at its own rank, which is the shape `cc-wu`'s flag
tower needs; `cc-thom`'s projectivised sum is the specialisation.

## Main declarations

* `hxi_trivOpen` — the class identification at a trivialising chart.
* `lerayHirschGraded_compact` — **Leray–Hirsch over a compact base**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory TopologicalSpace
open GroupApproximation.STW59
open GroupApproximation.CharClass.Bundle

noncomputable section

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The class identification at a trivialising chart.** -/
theorem hxi_trivOpen (q : Bundle X ι) (x₀ : X) (W : Opens (TopCat.of X)) (d : ℕ)
    (hrank : q.rank x₀ = d + 1 + 1) :
    pull (chartProdIsoOfHomeo q (trivOpen q x₀ ⊓ W) (d + 1)
          (projTrivStdOn q x₀ _ (trivInter_subset q x₀ W) (d + 1) hrank)).hom 2
        (pull (KnCP.cpSnd
          ↥((trivOpen q x₀ ⊓ W : Opens (TopCat.of X)) : Set X) (d + 1)) 2
          (cpGen (d + 1) (by omega)))
      = lhClass (projMapOf q) (tautEulerOf q) (trivOpen q x₀ ⊓ W) := by
  have hcard : d + 1 ≤ tautCardOf ι := by
    have h := rank_le_card q x₀
    rw [hrank] at h
    show d + 1 ≤ Fintype.card ι
    omega
  exact pull_prodIso_cpGen q (trivOpen q x₀ ⊓ W) (d + 1) (by omega) _
    (chartCPOf q x₀ (trivOpen q x₀ ⊓ W) (trivInter_subset q x₀ W) (d + 1) hrank) rfl
    (chartInclOf q (trivOpen q x₀ ⊓ W)) rfl hcard
    (chartTautIsoGen q x₀ (trivOpen q x₀ ⊓ W) (trivInter_subset q x₀ W) (d + 1) hrank)

/-- **Leray–Hirsch for a projectivised bundle over a compact base**, at every rank.
`H^*(P(q))` is free over `H^*(X)` on the powers of the tautological Euler class. -/
theorem lerayHirschGraded_compact [CompactSpace X] [Nonempty X]
    (q : Bundle X ι) (s : ℕ) (hs : ∀ x, q.rank x = s) (hs1 : 1 ≤ s) :
    LerayHirschGraded (projMapOf q) (tautEulerOf q) s := by
  match s, hs1 with
  | 1, _ =>
    exact lerayHirschGraded_rankOne q
      (fun x => by rw [trace_eq_rank, hs x]; norm_num) _
  | (d + 2), _ =>
    exact lerayHirschGraded_of_trivializing_cover q (projMapOf q) (tautEulerOf q) (d + 2)
      (fun x₀ W => LHOver_trivOpen q x₀ W d (hs x₀) (hxi_trivOpen q x₀ W d (hs x₀)))

end

end LH
end CharClass
end GroupApproximation
