import GroupApproximation.CharClass.ThomJmNaturalOf
import GroupApproximation.CharClass.ThomBridgeRelToAbsOf
import GroupApproximation.CharClass.ThomChartTautZero
import GroupApproximation.CharClass.CohomologyAssoc
import GroupApproximation.Meta.AxiomGuard

/-!
# The generic steps of `hclass`, over a field

Lane `lx-kunneth` of the STW Problem LIX strengthening, split item S1 of lane `lx-stepcK-agree`: the
field `jE u = π^* γ` of `KGen.KZeroStepCDataOf`.

`CharClass/LIXHclass.lean` proves at `F₂` that the absolute image of the Thom class is the pullback of
the top Chern class.  Every step but the last is stated for an abstract bundle and an abstract
Leray–Hirsch instance, and none of them uses the coefficient.  They are degree transports, the unit of
the cup product, a column term at a vanishing class, and naturality of column terms.  The last step
identifies the coordinates of the Thom class itself.  This file restates the generic steps over any
commutative ring, and the chart steps over a field, where the Thom bridge lives.

**The generator is a parameter.**  At `F₂` the Leray–Hirsch generator is the tautological class
`tautEulerOf p.plusOne`, and its vanishing on the affine chart is `LH.pull_bridgeChartIncl_tautEulerOf`.
Over `K` no generator is canonical (`lix-lh` works with `LH.tautEulerDualK K hgen`), so `ξ` is
arbitrary and its vanishing on the chart is the hypothesis `hξ`.

## Main declarations

* `gammaCoeff_eq_of_valOf`, `gamma_top_eq_chernCoeffOf`, `chernMul_top_unitOf` — the top Chern class
  as a coefficient.
* `lhTerm_zero_classOf`, `lhTerm_at_index_zeroOf` — column terms at the zero class and at index `0`.
* `pull_bridgeChartIncl_lhSumOf` — **restricting a Leray–Hirsch combination to the affine chart
  leaves the `i = 0` column**, whenever `ξ` dies on the chart.
* `relToAbs_bridgeTotalOf_eq_lhSumOf` — the bridged class is the combination of its Thom coordinates.
* `relToAbs_total_eq_pull_coordOf` — **the absolute image of a class of the vector-bundle pair is the
  pullback of its zeroth Thom coordinate.**  Once that coordinate is identified with the top Chern
  class, this is `hclass` over `K`.
-/

open CategoryTheory TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

open ThomChernDeg LH

set_option linter.unusedSectionVars false

/-! ## 1. The top Chern class as a coefficient -/

section Generic

variable {K : Type} [CommRing K] {X P : TopCat.{0}}

/-- Two Leray–Hirsch coefficients at indices with the same underlying natural number agree, after
the degree transport the index sits inside, over any commutative ring. -/
theorem gammaCoeff_eq_of_valOf {π : P ⟶ X} {ξ : Hmod K P 2} {r : ℕ}
    (L : LerayHirschGraded π ξ r) {k l : ℕ} (hk : k < lhDomainCard r (2 * r))
    (hl : l < lhDomainCard r (2 * r)) (h : k = l) :
    cohCast (show 2 * r - 2 * k = 2 * r - 2 * l by rw [h]) (L.gammaCoeff ⟨k, hk⟩)
      = L.gammaCoeff ⟨l, hl⟩ := by
  subst h
  exact cohCast_self _ _

/-- **The top Chern class is the zeroth reindexed coefficient**, over any commutative ring.
`gammaOf` reads it at index `r - r` and `chernCoeffOf` at index `0`. -/
theorem gamma_top_eq_chernCoeffOf {π : P ⟶ X} {ξ : Hmod K P 2} {r : ℕ}
    (L : LerayHirschGraded π ξ r) (hr : 1 ≤ r) :
    L.gamma r = chernCoeffOf L ⟨0, hr⟩ := by
  rw [L.gamma_eq_gammaOf hr (le_refl r)]
  exact gammaCoeff_eq_of_valOf L _ _ (Nat.sub_self r)

/-- **Multiplying the unit by the top Chern coefficient returns the top Chern class**, over any
commutative ring. -/
theorem chernMul_top_unitOf {π : P ⟶ X} {ξ : Hmod K P 2} {r : ℕ}
    (L : LerayHirschGraded π ξ r) (hr : 1 ≤ r) :
    chernMulOf L ⟨0, hr⟩ (cohCast (show (0 : ℕ) = 2 * r - 2 * r by omega) (one (K := K) X))
      = L.gamma r := by
  rw [chernMulOf_apply, cup_cohCast_left, one_cup', cohCast_cohCast, cohCast_cohCast,
    gamma_top_eq_chernCoeffOf L hr]
  exact cohCast_self _ _

/-! ## 2. Column terms at the zero class and at index zero -/

/-- A column above the zeroth vanishes at the zero class, over any commutative ring. -/
theorem lhTerm_zero_classOf (π : P ⟶ X) (n i : ℕ) (hi : 0 < i) (a : Hmod K X (n - 2 * i)) :
    lhTerm π (0 : Hmod K P 2) n i a = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
  by_cases h : 2 * (j + 1) ≤ n
  · rw [lhTerm_of_le π (0 : Hmod K P 2) h]
    have h0 : cupPowE (0 : Hmod K P 2) (j + 1) = 0 := by rw [cupPowE_succ, cup_zero]
    rw [h0, cup_zero, cohCast_zero]
  · rw [lhTerm_of_gt π (0 : Hmod K P 2) h]

/-- The zeroth column is the pullback, whatever the class, over any commutative ring. -/
theorem lhTerm_at_index_zeroOf (π : P ⟶ X) (ξ : Hmod K P 2) (n : ℕ) (a : Hmod K X (n - 2 * 0)) :
    lhTerm π ξ n 0 a = pull π n a := by
  rw [lhTerm_of_le π ξ (show 2 * 0 ≤ n by omega), cupPowE_zero, cup_one]
  exact cohCast_self _ _

end Generic

/-! ## 3. Restricting a Leray–Hirsch combination to the affine chart -/

section Chart

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **A Leray–Hirsch combination restricted to the affine chart is its zeroth column**, over any
commutative ring, for any generator `ξ` that dies on the chart.  Every higher column carries a cup
power of `ξ`, and the zeroth column is the pullback along the bundle projection because the chart
inclusion lies over the base. -/
theorem pull_bridgeChartIncl_lhSumOf {K : Type} [CommRing K] (p : Bundle X ι)
    (ξ : Hmod K (TopCat.of (Bundle.Proj p.plusOne)) 2)
    (hξ : pull (cmap (bridgeChartIncl p)) 2 ξ = 0) (r : ℕ) (hr : 1 ≤ r)
    (a : (i : Fin (r + 1)) → Hmod K (TopCat.of X) (2 * r - 2 * (i : ℕ))) :
    pull (cmap (bridgeChartIncl p)) (2 * r)
        (∑ i : Fin (r + 1), lhTerm (projMapOf p.plusOne) ξ (2 * r) (i : ℕ) (a i))
      = pull (cmap (Bundle.totalPi p)) (2 * r) (a ((⟨0, hr⟩ : Fin r).castSucc)) := by
  have hterm : ∀ i : Fin (r + 1),
      pull (cmap (bridgeChartIncl p)) (2 * r)
          (lhTerm (projMapOf p.plusOne) ξ (2 * r) (i : ℕ) (a i))
        = lhTerm (cmap (Bundle.totalPi p))
            (0 : Hmod K (TopCat.of (Bundle.Total p)) 2) (2 * r) (i : ℕ) (a i) := fun i =>
    LHCast.pull_lhTermOf (cmap (bridgeChartIncl p)) (projMapOf p.plusOne)
      (cmap (Bundle.totalPi p)) (bridgeChartIncl_comp_projMapOf p) ξ 0 hξ (2 * r) (i : ℕ) (a i)
  rw [pull_sum]
  simp only [hterm]
  rw [Finset.sum_eq_single ((⟨0, hr⟩ : Fin r).castSucc)]
  · exact lhTerm_at_index_zeroOf _ _ _ _
  · intro b _ hb
    refine lhTerm_zero_classOf _ _ _ ?_ _
    rcases Nat.eq_zero_or_pos (b : ℕ) with h0 | h0
    · exact absurd (Fin.val_injective h0) hb
    · exact h0
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ## 4. The absolute image of a class of the vector-bundle pair -/

/-- **The bridged class is the Leray–Hirsch combination of its Thom coordinates**, over a field. -/
theorem relToAbs_bridgeTotalOf_eq_lhSumOf (K : Type) [Field K] [CompactSpace X] [T2Space X]
    (p : Bundle X ι) {r : ℕ} {ξ : Hmod K (TopCat.of (Bundle.Proj p.plusOne)) 2}
    (L : LerayHirschGraded (projMapOf p.plusOne) ξ (r + 1))
    (u : ↥(relCohomology K (TopCat.of (Bundle.Total p))
      ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p) (2 * r))) :
    (relToAbs K (TopCat.of (Bundle.Proj p.plusOne)) (Set.range (Bundle.projIncl p)) (2 * r)).hom
        (bridgeTotalOf K p (2 * r) u)
      = ∑ i : Fin (r + 1),
          lhTerm (projMapOf p.plusOne) ξ (2 * r) (i : ℕ) (thomJmTotalOf K p L u i) := by
  have h1 : (lhTopEquivOf L).symm
      ((relToAbs K (TopCat.of (Bundle.Proj p.plusOne)) (Set.range (Bundle.projIncl p))
        (2 * r)).hom (bridgeTotalOf K p (2 * r) u))
      = thomJmTotalOf K p L u := by
    rw [thomJmTotalOf_apply, thomJmOf_apply]
  have h2 : (relToAbs K (TopCat.of (Bundle.Proj p.plusOne)) (Set.range (Bundle.projIncl p))
        (2 * r)).hom (bridgeTotalOf K p (2 * r) u)
      = (lhTopEquivOf L) (thomJmTotalOf K p L u) := by
    rw [← h1, LinearEquiv.apply_symm_apply]
  rw [h2]
  rfl

/-- **The absolute image of a class of the vector-bundle pair is the pullback of its zeroth Thom
coordinate**, over a field, for any Leray–Hirsch generator that dies on the affine chart.  With the
zeroth coordinate identified as the top Chern class, this is `hclass` over `K`: it is
`CharClass/LIXHclass.lean`'s argument with the Thom class left arbitrary. -/
theorem relToAbs_total_eq_pull_coordOf (K : Type) [Field K] [CompactSpace X] [T2Space X]
    (p : Bundle X ι) {r : ℕ} (hr : 1 ≤ r) {ξ : Hmod K (TopCat.of (Bundle.Proj p.plusOne)) 2}
    (hξ : pull (cmap (bridgeChartIncl p)) 2 ξ = 0)
    (L : LerayHirschGraded (projMapOf p.plusOne) ξ (r + 1))
    (u : ↥(relCohomology K (TopCat.of (Bundle.Total p))
      ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p) (2 * r))) :
    (relToAbs K (TopCat.of (Bundle.Total p))
        ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p) (2 * r)).hom u
      = pull (cmap (Bundle.totalPi p)) (2 * r)
          (thomJmTotalOf K p L u ((⟨0, hr⟩ : Fin r).castSucc)) := by
  refine (relToAbs_bridgeTotalOf K p (2 * r) u).trans ?_
  rw [relToAbs_bridgeTotalOf_eq_lhSumOf K p L u]
  exact pull_bridgeChartIncl_lhSumOf p ξ hξ r hr (thomJmTotalOf K p L u)

end Chart

end

/-! Audited on every build: `#audit_axioms` fails the build if a closure leaves the classical
allowlist. -/

#audit_axioms chernMul_top_unitOf
#audit_axioms pull_bridgeChartIncl_lhSumOf
#audit_axioms relToAbs_total_eq_pull_coordOf

end GroupApproximation.CharClass
