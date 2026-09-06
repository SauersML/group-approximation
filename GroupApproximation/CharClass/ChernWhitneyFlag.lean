import GroupApproximation.CharClass.ChernSplittingData
import GroupApproximation.CharClass.ChernClasses
import GroupApproximation.CharClass.ChernRelation

/-!
# Whitney on the flag bundle

The last field of `cc-wu`'s splitting data: pulled back to a space where the bundle
splits, the `k`-th Chern class is the `k`-th elementary symmetric function of the
roots.

Once the splitting is stated as an identity of *polynomials* there is no geometry
left in it.  The Chern classes are by definition the coefficients of the monic
relation the tautological class satisfies, so pulling them back is mapping that
polynomial's coefficients; and Vieta reads the coefficients of a product of linear
factors as elementary symmetric functions.  Both sides also vanish above the rank,
for the two different reasons that make the statement hold for every `k` and not
only in range.

So the hypothesis carried here is the split form of the relation, which is what a
flag-bundle construction produces and what `ChernRelation.chernPoly_eq_prod_of_root`
turns a vanishing product into.  Nothing about flags, projectivisations or
Leray–Hirsch appears below.

## Main declarations

* `LerayHirschData.chern_eq_coeff` — the Chern class is the named coefficient.
* `chern_split_of_splitPoly` — **Whitney on the flag bundle**, for every `k`.
* `splittingDataOfSplitPoly`, `hasSplitting_of_splitPoly` — `cc-wu`'s splitting
  data with the last field discharged.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory Polynomial

noncomputable section

namespace LerayHirschData

variable {X P : TopCat.{0}} (D : LerayHirschData X P)

/-- The `k`-th Chern class is the coefficient of the relation in degree
`rank - k`.  `chernClass_of_le` at the power basis, whose dimension is the rank by
`rfl`. -/
theorem chern_eq_coeff {i : ℕ} (hi : i ≤ D.rank) :
    D.chern i = D.chernPolynomial.coeff (D.rank - i) :=
  @chernClass_of_le (TotalH X) (TotalH P) _ _ D.algebra D.powerBasis i hi

end LerayHirschData

/-- **Whitney on the flag bundle.**  If the Chern polynomial splits into linear
factors after pullback, its coefficients are the elementary symmetric functions of
the roots.

In range this is Vieta plus the definition of the Chern classes as coefficients.
Above the rank both sides vanish: the left because the relation has degree the
rank, the right because a set of that size has no subsets of larger cardinality. -/
theorem chern_split_of_splitPoly {N F P : TopCat.{0}} (D : LerayHirschData N P)
    (proj : F ⟶ N) (r : ℕ) (hr : D.rank = r) (root : ℕ → Hmod2 F 2)
    (hsplit : D.chernPolynomial.map (TotalH.map proj)
      = ∏ l ∈ Finset.range r, (X + C (TotalH.of F 2 (root l))))
    (k : ℕ) :
    TotalH.map proj (D.chern k)
      = esymmOn (Finset.range r) (fun l => TotalH.of F 2 (root l)) k := by
  subst hr
  by_cases hk : k ≤ D.rank
  · have hcoeff : TotalH.map proj (D.chern k)
        = (D.chernPolynomial.map (TotalH.map proj)).coeff (D.rank - k) := by
      rw [Polynomial.coeff_map, D.chern_eq_coeff hk]
    rw [hcoeff, hsplit,
      Finset.prod_X_add_C_coeff _ _ (by rw [Finset.card_range]; omega), esymmOn_def]
    congr 2
    rw [Finset.card_range]
    omega
  · replace hk : D.rank < k := by omega
    have h1 : D.chern k = 0 := D.chern_eq_zero_of_lt hk
    have h2 : esymmOn (Finset.range D.rank) (fun l => TotalH.of F 2 (root l)) k = 0 := by
      rw [esymmOn_def,
        Finset.powersetCard_eq_empty.mpr (by rw [Finset.card_range]; omega)]
      exact Finset.sum_empty
    rw [h1, h2, map_zero]

/-- **`cc-wu`'s splitting data, with every field discharged** except the two
geometric inputs: a Leray–Hirsch instance on the flag bundle and the split form of
the relation there. -/
def splittingDataOfSplitPoly {N F P : TopCat.{0}} (D : LerayHirschData N P)
    (proj : F ⟶ N) (ξ : Hmod2 F 2) (rk : ℕ) (hrk : 0 < rk)
    (L : LerayHirschGraded proj ξ rk)
    (r : ℕ) (hr : D.rank = r) (root : ℕ → Hmod2 F 2)
    (hroot : ∀ l : ℕ, ∃ (d : ℕ) (g : F ⟶ CPtop d) (h : Hmod2 (CPtop d) 2),
      root l = pull g 2 h)
    (hsplit : D.chernPolynomial.map (TotalH.map proj)
      = ∏ l ∈ Finset.range r, (X + C (TotalH.of F 2 (root l)))) :
    Wu.SplittingData N F r D.chern :=
  LH.splittingDataOfGraded proj ξ rk hrk L root hroot
    (chern_split_of_splitPoly D proj r hr root hsplit)

/-- The same with the flag space hidden. -/
theorem hasSplitting_of_splitPoly {N F P : TopCat.{0}} (D : LerayHirschData N P)
    (proj : F ⟶ N) (ξ : Hmod2 F 2) (rk : ℕ) (hrk : 0 < rk)
    (L : LerayHirschGraded proj ξ rk)
    (r : ℕ) (hr : D.rank = r) (root : ℕ → Hmod2 F 2)
    (hroot : ∀ l : ℕ, ∃ (d : ℕ) (g : F ⟶ CPtop d) (h : Hmod2 (CPtop d) 2),
      root l = pull g 2 h)
    (hsplit : D.chernPolynomial.map (TotalH.map proj)
      = ∏ l ∈ Finset.range r, (X + C (TotalH.of F 2 (root l)))) :
    Wu.HasSplitting N D.chern :=
  ⟨F, r, ⟨splittingDataOfSplitPoly D proj ξ rk hrk L r hr root hroot hsplit⟩⟩

end

end CharClass
end GroupApproximation
