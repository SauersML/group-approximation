import GroupApproximation.CharClass.CohomologyLHRingComponent

/-!
# Injectivity of the ring-level Leray–Hirsch combination

Half of `LerayHirschData.free`, and the half that needs no finite-support
argument.

If the ring-level combination of a tuple vanishes then every degree gives a
vanishing degreewise tuple.  To reach a fixed coefficient `c i` in a fixed degree
`m`, choose the degree `2i + m`: there the index `i` is in range, because `i < r`
and `2i ≤ 2i + m`, which is exactly `mem_lhDomain_iff`.  So every component of
every coefficient vanishes, and a direct-sum element with no components is zero.

The choice of degree is the whole trick, and it is available only because the
contributing indices form an initial segment.

## Main declarations

* `LHCast.lhFun_injective` — **injectivity**, from the degreewise statement.
-/

open CategoryTheory

namespace GroupApproximation.CharClass

noncomputable section

namespace LHCast

open LH

variable {X P : TopCat.{0}}

set_option maxHeartbeats 1000000 in
/-- **The ring-level combination is injective.**  Reach the `i`-th coefficient in
degree `m` by looking at degree `2i + m`, where `i` is in range. -/
theorem lhFun_injective {π : P ⟶ X} {ξ : Hmod2 P 2} {r : ℕ}
    (L : LerayHirschGraded π ξ r) : Function.Injective (lhFun π r ξ) := by
  intro c c' h
  funext i
  ext m
  have hn : (i : ℕ) < lhDomainCard r (2 * (i : ℕ) + m) :=
    (mem_lhDomain_iff r (2 * (i : ℕ) + m) (i : ℕ)).mpr ⟨i.isLt, by omega⟩
  have hcomp := congrArg (TotalH.component P (2 * (i : ℕ) + m)) h
  rw [component_lhFun, component_lhFun] at hcomp
  have hval := congrFun ((L.bij (2 * (i : ℕ) + m)).1 hcomp) ⟨(i : ℕ), hn⟩
  simp only [degFun, dif_pos i.isLt] at hval
  have hm : 2 * (i : ℕ) + m - 2 * (i : ℕ) = m := by omega
  show TotalH.component X m (c i) = TotalH.component X m (c' i)
  rw [← hm]
  exact hval

end LHCast

end

end GroupApproximation.CharClass
