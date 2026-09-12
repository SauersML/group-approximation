import GroupApproximation.CharClass.LerayHirschChartTautGenOf
import GroupApproximation.CharClass.LerayHirschTrivOpenOf
import GroupApproximation.CharClass.LerayHirschBundleOf
import GroupApproximation.CharClass.LerayHirschRankOneOf
import GroupApproximation.CharClass.LerayHirschNegOf

/-!
# Leray–Hirsch for a projectivised bundle over a compact base, over a field

The coefficient-generic form of `LerayHirschCompact`.  The proof splits on the rank and only on the
rank, exactly as over `F₂`.  At rank one the projection is a homeomorphism
(`lerayHirschGraded_rankOneOf`, for every class).  Above it the cover induction over the trivialising
sets runs over a field (`lerayHirschGraded_of_trivializing_coverOf`), and each chart step
(`LHOver_trivOpenOf`) consumes the class identification at the chart, `hxi_trivOpenOf`, whose fibre
class is the restriction `fibClassOf K hgen (d+1) _` of the chosen class `hgen`, nonzero when `hgen`
is (`fibClassOf_ne_zero`).

The one input is the free-module statement for `U × ℂP^{d+1}` with a nonzero fibre class, and it
is taken as a hypothesis here, only in the ranks the statement uses (`d + 2 ≤ s`): the `K` free tuple
is built in `LerayHirschLadderClosedOf`, and at rank two it is unconditional
(`hasFreeTuple_cpProd_zeroOf`), which is what the ring of `ℂP^d` over `K` needs.

The dual class `tautEulerDualK = −tautEulerOfK`, the one the splitting principle is stated with,
comes for free (`lerayHirschGraded_neg`).

## Main declarations

* `lerayHirschGraded_compactOf_of_freeTuple` — **Leray–Hirsch over a compact base, over a field**,
  over the free tuple in the ranks it uses.
* `lerayHirschGraded_compactDualOf_of_freeTuple` — the same for `tautEulerDualK`.
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

/-- **Leray–Hirsch for a projectivised bundle over a compact base, over a field**, at every rank,
for every nonzero class `hgen ∈ H^2(ℂP^{1 + card ι}; K)`, over the free-module statement for a
product with `ℂP^{d+1}` in the ranks `d + 2 ≤ s`.  `H^*(P(q); K)` is free over `H^*(X; K)` on the
powers of the tautological class. -/
theorem lerayHirschGraded_compactOf_of_freeTuple (K : Type) [Field K] [CompactSpace X]
    [Nonempty X] (q : Bundle X ι) (s : ℕ) (hs : ∀ x, q.rank x = s) (hs1 : 1 ≤ s)
    (hgen : Hmod K (CPtop (1 + tautCardOf ι)) 2) (hgen0 : hgen ≠ 0)
    (hfree : ∀ (U : Type) [TopologicalSpace U] (d : ℕ), d + 2 ≤ s →
      ∀ hfib : Hmod K (CPtop (d + 1)) 2, hfib ≠ 0 →
        HasFreeTuple (KnCP.cpFst U (d + 1)) (pull (KnCP.cpSnd U (d + 1)) 2 hfib) (d + 1 + 1)) :
    LerayHirschGraded (projMapOf q) (tautEulerOfK K hgen q) s := by
  match s, hs1 with
  | 1, _ =>
    exact lerayHirschGraded_rankOneOf K q
      (fun x => by rw [trace_eq_rank, hs x]; norm_num) _
  | (d + 2), _ =>
    exact lerayHirschGraded_of_trivializing_coverOf K q (projMapOf q) (tautEulerOfK K hgen q)
      (d + 2)
      (fun x₀ W => LHOver_trivOpenOf K q x₀ W d (hs x₀)
        (fibClassOf K hgen (d + 1) (rank_le_one_add_tautCardOf q x₀ d (hs x₀)))
        (hfree ↥((trivOpen q x₀ ⊓ W : Opens (TopCat.of X)) : Set X) d le_rfl _
          (fibClassOf_ne_zero K hgen hgen0 (by omega)
            (rank_le_one_add_tautCardOf q x₀ d (hs x₀))))
        (tautEulerOfK K hgen q)
        (hxi_trivOpenOf K q x₀ W d (hs x₀) hgen))

/-- **The same for the dual tautological class** `tautEulerDualK = −tautEulerOfK`, the class the
splitting principle over `K` is stated with. -/
theorem lerayHirschGraded_compactDualOf_of_freeTuple (K : Type) [Field K] [CompactSpace X]
    [Nonempty X] (q : Bundle X ι) (s : ℕ) (hs : ∀ x, q.rank x = s) (hs1 : 1 ≤ s)
    (hgen : Hmod K (CPtop (1 + tautCardOf ι)) 2) (hgen0 : hgen ≠ 0)
    (hfree : ∀ (U : Type) [TopologicalSpace U] (d : ℕ), d + 2 ≤ s →
      ∀ hfib : Hmod K (CPtop (d + 1)) 2, hfib ≠ 0 →
        HasFreeTuple (KnCP.cpFst U (d + 1)) (pull (KnCP.cpSnd U (d + 1)) 2 hfib) (d + 1 + 1)) :
    LerayHirschGraded (projMapOf q) (tautEulerDualK K hgen q) s :=
  lerayHirschGraded_neg (lerayHirschGraded_compactOf_of_freeTuple K q s hs hs1 hgen hgen0 hfree)

end

end LH
end CharClass
end GroupApproximation
