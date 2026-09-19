import GroupApproximation.CharClass.ChernSplitRelation

/-!
# The split relation with the hypotheses restricted to the range

`cc-wu` found that `splitRelation_of_sum`'s trace hypothesis is quantified over
every index, while the only indices that appear are those below the rank, and
that at the flag the difference is not a matter of convenience: `flagLine p r l`
is *zero* for `l ≥ r`, so its trace is zero and the unrestricted hypothesis is
**false** there.  No family built from the flag can satisfy it.  The same is true
of this lane's own flattened family of the lines of `V`, which is zero off the
range by construction.

So the hypotheses are restricted here.  The proofs are unchanged, because the
induction only ever reaches indices below the rank; what changes is which
statement a consumer has to supply.

The root family is also taken as a **parameter** agreeing with the Euler classes
only on the range, which is `cc-wu`'s second point and worth having on its own:
with the roots computed from the trace proof, a consumer supplying a different
proof of the same trace condition gets a syntactically different family, and the
conclusion carries a dependent proof argument it does not need.

Under rule 11 the published names stay; these are new ones.

## Main declarations

* `exists_prod_vanishing_on_coverSup_lt`, `prod_eq_zero_of_cover_lt` — the
  iteration, with the vanishing hypothesis restricted.
* `splitRelation_of_sum_lt` — **the split relation**, in the form a flag family
  or a family zero off the range can actually supply.
-/

set_option autoImplicit false

namespace GroupApproximation.CharClass

open CategoryTheory TopologicalSpace
open GroupApproximation.CharClass.Bundle
open GroupApproximation.CharClass.LH
open GroupApproximation.CharClass.CPn
open GroupApproximation.CharClass.LHCast

noncomputable section

/-! ## 1. The iteration, restricted -/

variable {X : TopCat.{0}}

/-- The induction, with the vanishing hypothesis only below `r`. -/
theorem exists_prod_vanishing_on_coverSup_lt (U : ℕ → Opens X) (d : ℕ) (hd : 0 < d)
    (a : ℕ → Hmod2 X d) (r : ℕ) (ha : ∀ l, l < r → pull (opIncl (U l)) d (a l) = 0) :
    ∀ k : ℕ, k < r → ∃ (m : ℕ) (c : Hmod2 X m), 0 < m ∧
      (∏ l ∈ Finset.range (k + 1), TotalH.of X d (a l)) = TotalH.of X m c ∧
      pull (opIncl (coverSup U (k + 1))) m c = 0 := by
  intro k
  induction k with
  | zero =>
      intro hk
      refine ⟨d, a 0, hd, ?_, ?_⟩
      · rw [Finset.prod_range_one]
      · rw [coverSup_one]
        exact ha 0 hk
  | succ k ih =>
      intro hk
      obtain ⟨m, c, hm, hprod, hvan⟩ := ih (by omega)
      refine ⟨m + d, cup c (a (k + 1)), by omega, ?_, ?_⟩
      · rw [Finset.prod_range_succ, hprod, TotalH.of_mul]
      · exact pull_cup_eq_zero_of_eq_sup (coverSup U (k + 1)) (U (k + 1))
          (coverSup U (k + 1 + 1)) (coverSup_succ U (k + 1)) (by omega) c (a (k + 1))
          hvan (ha (k + 1) hk)

/-- **A product over a finite open cover vanishes**, with the vanishing hypothesis
only below `r`. -/
theorem prod_eq_zero_of_cover_lt (U : ℕ → Opens X) (r : ℕ) (hr : 0 < r)
    (hcov : coverSup U r = ⊤) (d : ℕ) (hd : 0 < d) (a : ℕ → Hmod2 X d)
    (ha : ∀ l, l < r → pull (opIncl (U l)) d (a l) = 0) :
    (∏ l ∈ Finset.range r, TotalH.of X d (a l)) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  obtain ⟨m, c, _hm, hprod, hvan⟩ :=
    exists_prod_vanishing_on_coverSup_lt U d hd a (k + 1) ha k (by omega)
  rw [hcov] at hvan
  rw [hprod, eq_zero_of_pull_opIncl_top hvan, map_zero]

/-! ## 2. The split relation, restricted -/

variable {Y : Type} [TopologicalSpace Y] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The split relation**, with the trace hypothesis only below the rank and the
roots taken as a parameter.  This is the form a flag family supplies, and the form
a family that is zero off the range supplies. -/
theorem splitRelation_of_sum_lt [CompactSpace Y] [Nonempty Y]
    (p : Bundle Y ι) (r : ℕ) (hr1 : 1 ≤ r) (hrank : ∀ x, p.rank x = r)
    (qf : ℕ → Bundle Y ι) (hq : ∀ l, l < r → ∀ x, (qf l x).trace = 1)
    (hsum : ∀ x, p x = ∑ l ∈ Finset.range r, qf l x)
    (root : ℕ → Hmod2 (TopCat.of Y) 2)
    (hroot : ∀ l, ∀ hl : l < r, root l = lineEulerOf (qf l) (hq l hl)) :
    LerayHirschData.SplitRelation
      (lerayHirschData_of_graded (lerayHirschGraded_compact p r hrank hr1)) r root := by
  show (∏ l ∈ Finset.range r,
      (TotalH.of (TopCat.of (Proj p)) 2 (tautEulerOf p)
        + TotalH.map (projMapOf p) (TotalH.of (TopCat.of Y) 2 (root l)))) = 0
  have hfac : ∀ l : ℕ,
      (TotalH.of (TopCat.of (Proj p)) 2 (tautEulerOf p)
        + TotalH.map (projMapOf p) (TotalH.of (TopCat.of Y) 2 (root l)))
      = TotalH.of (TopCat.of (Proj p)) 2
          (tautEulerOf p + pull (projMapOf p) 2 (root l)) := by
    intro l
    rw [TotalH.map_of, map_add]
  rw [Finset.prod_congr rfl (fun l (_ : l ∈ Finset.range r) => hfac l)]
  refine prod_eq_zero_of_cover_lt (fun l => lineOpens p (qf l)) r hr1
    (coverSup_lineOpens p r qf hsum) 2 (by omega) _ ?_
  intro l hl
  rw [hroot l hl]
  exact pull_factor_eq_zero p (qf l) (hq l hl)

end

end GroupApproximation.CharClass
