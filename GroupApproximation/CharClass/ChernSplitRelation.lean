import GroupApproximation.CharClass.CupVanishIterate
import GroupApproximation.CharClass.ChernSplitFactor
import GroupApproximation.CharClass.ChernFactorBridge
import GroupApproximation.CharClass.LerayHirschCompact
import GroupApproximation.CharClass.CohomologyLHRingData

/-!
# The split relation, for a bundle that is a sum of lines

Everything is in place, so this is the assembly.

Each factor `ξ + π^*e(L_l)` restricts to zero on the locus where the `l`-th
summand does not kill the tautological line, because there the two line bundles
are isomorphic and so have the same Euler class, and over `ZMod 2` a sum of two
equal classes is zero.  Those loci cover, because a nonzero vector in a direct sum
has a nonzero component.  So the product of the factors is zero, which is
`SplitRelation`, and `splitPoly_of_splitRelation` turns it into the factorisation
of the Chern polynomial.

No tensor product and no additivity of the Euler class appears anywhere; the roots
come out as the Euler classes of the summands directly.

## Main declarations

* `lineOpens` — `cc-bundle`'s locus, as an `Opens`.
* `pull_factor_eq_zero` — **each factor vanishes on its own open set.**
* `splitRelation_of_sum` — **the split relation.**
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory TopologicalSpace
open GroupApproximation.CharClass.Bundle
open GroupApproximation.CharClass.LH
open GroupApproximation.CharClass.CPn
open GroupApproximation.CharClass.LHCast

noncomputable section

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `cc-bundle`'s locus, bundled as an `Opens`. -/
def lineOpens (p q : Bundle X ι) : Opens (TopCat.of (Proj p)) :=
  ⟨lineOpenSet p q, isOpen_lineOpenSet p q⟩

/-- **Each factor vanishes on its own open set.**  The two Euler classes agree
there, and over `ZMod 2` a class plus itself is zero. -/
theorem pull_factor_eq_zero (p q : Bundle X ι) (hq : ∀ x, (q x).trace = 1) :
    pull (opIncl (lineOpens p q)) 2
        (tautEulerOf p + pull (projMapOf p) 2 (lineEulerOf q hq)) = 0 := by
  have hd : (1 : ℕ) ≤ 1 + tautCardOf ι := by omega
  have h1 : pull (opIncl (lineOpens p q)) 2 (tautEulerOf p)
      = lineEulerOf (Bundle.restrictTo (tautLine p) (lineOpenSet p q))
          (fun y => trace_tautLine p (y : Proj p)) :=
    (eulerOfBundle_comap hd
      (pushforward (tautEmbOf ι) (tautEmbOf_injective ι) (tautLine p)) _
      ⟨Subtype.val, continuous_subtype_val⟩).symm
  have h2 : pull (opIncl (lineOpens p q)) 2 (pull (projMapOf p) 2 (lineEulerOf q hq))
      = lineEulerOf (Bundle.restrictTo (comap (projPi p) q) (lineOpenSet p q))
          (fun y => hq (projPi p (y : Proj p))) := by
    rw [← pull_comp]
    exact (eulerOfBundle_comap hd
      (pushforward (tautEmbOf ι) (tautEmbOf_injective ι) q) _
      ((projPi p).comp ⟨Subtype.val, continuous_subtype_val⟩)).symm
  rw [pull_add, h1, h2, eulerOf_restrict_eq p q hq]
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from by decide, zero_smul]

omit [DecidableEq ι] in
/-- **The loci cover.** -/
theorem coverSup_lineOpens (p : Bundle X ι) (r : ℕ) (qf : ℕ → Bundle X ι)
    (hsum : ∀ x, p x = ∑ l ∈ Finset.range r, qf l x) :
    coverSup (fun l => lineOpens p (qf l)) r = ⊤ := by
  refine Opens.ext (Set.eq_univ_of_forall fun z => ?_)
  obtain ⟨l, hl, hz⟩ := exists_mem_lineOpenSet p r qf hsum z
  exact (Finset.le_sup (f := fun l => lineOpens p (qf l)) hl) hz

/-- **The split relation**, for a bundle over a compact non-empty base that is a
sum of `r` line bundles.  The roots are the Euler classes of the summands. -/
theorem splitRelation_of_sum [CompactSpace X] [Nonempty X]
    (p : Bundle X ι) (r : ℕ) (hr1 : 1 ≤ r) (hrank : ∀ x, p.rank x = r)
    (qf : ℕ → Bundle X ι) (hq : ∀ l x, (qf l x).trace = 1)
    (hsum : ∀ x, p x = ∑ l ∈ Finset.range r, qf l x) :
    LerayHirschData.SplitRelation
      (lerayHirschData_of_graded (lerayHirschGraded_compact p r hrank hr1)) r
      (fun l => lineEulerOf (qf l) (hq l)) := by
  show (∏ l ∈ Finset.range r,
      (TotalH.of (TopCat.of (Proj p)) 2 (tautEulerOf p)
        + TotalH.map (projMapOf p)
            (TotalH.of (TopCat.of X) 2 (lineEulerOf (qf l) (hq l))))) = 0
  have hfac : ∀ l : ℕ,
      (TotalH.of (TopCat.of (Proj p)) 2 (tautEulerOf p)
        + TotalH.map (projMapOf p)
            (TotalH.of (TopCat.of X) 2 (lineEulerOf (qf l) (hq l))))
      = TotalH.of (TopCat.of (Proj p)) 2
          (tautEulerOf p + pull (projMapOf p) 2 (lineEulerOf (qf l) (hq l))) := by
    intro l
    rw [TotalH.map_of, map_add]
  rw [Finset.prod_congr rfl (fun l (_ : l ∈ Finset.range r) => hfac l)]
  exact prod_eq_zero_of_cover (fun l => lineOpens p (qf l)) r hr1
    (coverSup_lineOpens p r qf hsum) 2 (by omega) _
    (fun l => pull_factor_eq_zero p (qf l) (hq l))

end

end CharClass
end GroupApproximation
