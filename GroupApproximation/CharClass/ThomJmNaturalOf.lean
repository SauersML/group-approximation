import GroupApproximation.CharClass.ThomJmNatural
import GroupApproximation.CharClass.ThomBridgeTotalNaturalOf
import GroupApproximation.Meta.AxiomGuard

/-!
# The Thom coordinates over a field are natural

Lane `lix-thom` of the stronger LIX programme (`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`
§1.5), successor of `sp-thom`.

`ThomJmNatural` shows at `F₂` that the Leray–Hirsch coordinates of a relative class are
natural under a map of projections over a map of bases, and, at the vector-bundle pair, under
a restriction of the base.  Both sides are determined by the same combination of column
terms, so nothing about exactness enters: it is `relToAbs_naturality`, then a base change of
column terms inside the sum, read back through the coordinate equivalence.  Over any
commutative ring these are `lhTopEquivOf`, `LHCast.pull_lhTermOf` and `relToAbs_naturality K`.

At the vector-bundle pair over a field the Leray–Hirsch generators `ξ`, `ξ'` are arbitrary,
with the compatibility `hξ` a hypothesis.  For the tautological classes over `K` it is
`lix-lh`'s `eulerOfBundle_comapOf`.

## Main declarations

* `LH.pull_lhTerm_baseOf` — a column term under a base change, over any ring.
* `ThomChernDeg.thomJm_naturalOf` — **the coordinates are natural, over any ring**.
* `ThomChernDeg.thomJmTotalOf`, `thomJmTotal_restrictOf` — the coordinates of the vector-bundle
  pair over a field, under a base restriction.
-/

set_option autoImplicit false

open CategoryTheory TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

set_option linter.unusedSectionVars false

namespace LH

/-- **A Leray–Hirsch column term pulls back to the column term at the same index**, along a
map of projections over a map of bases, over any commutative ring. -/
theorem pull_lhTerm_baseOf {K : Type} [CommRing K] {X X' P P' : TopCat.{0}} (g : P' ⟶ P)
    (fb : X' ⟶ X) (π : P ⟶ X) (π' : P' ⟶ X') (hsq : g ≫ π = π' ≫ fb)
    (ξ : Hmod K P 2) (ξ' : Hmod K P' 2) (hξ : pull g 2 ξ = ξ')
    (n i : ℕ) (a : Hmod K X (n - 2 * i)) :
    pull g n (lhTerm π ξ n i a) = lhTerm π' ξ' n i (pull fb (n - 2 * i) a) := by
  rw [LHCast.pull_lhTermOf g π (π' ≫ fb) hsq ξ ξ' hξ n i a]
  by_cases hi : 2 * i ≤ n
  · rw [lhTerm_of_le (π' ≫ fb) ξ' hi, lhTerm_of_le π' ξ' hi, pull_comp]
  · rw [lhTerm_of_gt (π' ≫ fb) ξ' hi, lhTerm_of_gt π' ξ' hi]

end LH

namespace ThomChernDeg

open LH

@[simp] theorem lhSumTopOf_apply {K : Type} [CommRing K] {X P : TopCat.{0}} (π : P ⟶ X)
    (ξ : Hmod K P 2) (r : ℕ) (a : (i : Fin (r + 1)) → Hmod K X (2 * r - 2 * (i : ℕ))) :
    lhSumTopOf π ξ r a = ∑ i : Fin (r + 1), lhTerm π ξ (2 * r) (i : ℕ) (a i) := rfl

set_option maxHeartbeats 1000000 in
/-- **The Leray–Hirsch coordinates of a relative class are natural**, over any commutative
ring. -/
theorem thomJm_naturalOf {K : Type} [CommRing K] {X X' P P' : TopCat.{0}} {π : P ⟶ X}
    {ξ : Hmod K P 2} {π' : P' ⟶ X'} {ξ' : Hmod K P' 2} {r : ℕ}
    (L : LerayHirschGraded π ξ (r + 1)) (L' : LerayHirschGraded π' ξ' (r + 1))
    (g : P' ⟶ P) (fb : X' ⟶ X) (hsq : g ≫ π = π' ≫ fb) (hξ : pull g 2 ξ = ξ')
    {Z : Set P} {Z' : Set P'} (hZ : ∀ z ∈ Z', (ConcreteCategory.hom g) z ∈ Z)
    (x : ↥(relCohomology K P Z (2 * r))) :
    thomJmOf K (lhTopEquivOf L') Z' ((relPullback K g hZ (2 * r)).hom x)
      = fun i : Fin (r + 1) =>
          pull fb (2 * r - 2 * (i : ℕ)) (thomJmOf K (lhTopEquivOf L) Z x i) := by
  have hrel : (relToAbs K P' Z' (2 * r)).hom ((relPullback K g hZ (2 * r)).hom x)
      = pull g (2 * r) ((relToAbs K P Z (2 * r)).hom x) := by
    have h := congrArg (fun t => t.hom x) (relToAbs_naturality K g hZ (2 * r))
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h
    exact h.symm
  have hL : lhSumTopOf π ξ r (thomJmOf K (lhTopEquivOf L) Z x)
      = (relToAbs K P Z (2 * r)).hom x := by
    show (lhTopEquivOf L) (thomJmOf K (lhTopEquivOf L) Z x) = _
    exact (lhTopEquivOf L).apply_symm_apply _
  have hsum : lhSumTopOf π' ξ' r
        (fun i : Fin (r + 1) =>
          pull fb (2 * r - 2 * (i : ℕ)) (thomJmOf K (lhTopEquivOf L) Z x i))
      = (relToAbs K P' Z' (2 * r)).hom ((relPullback K g hZ (2 * r)).hom x) := by
    rw [hrel, ← hL, lhSumTopOf_apply, lhSumTopOf_apply, pull_sum]
    exact Finset.sum_congr rfl fun (i : Fin (r + 1)) _ =>
      (pull_lhTerm_baseOf g fb π π' hsq ξ ξ' hξ (2 * r) (i : ℕ)
        (thomJmOf K (lhTopEquivOf L) Z x i)).symm
  show (lhTopEquivOf L').symm ((relToAbs K P' Z' (2 * r)).hom
      ((relPullback K g hZ (2 * r)).hom x)) = _
  rw [← hsum]
  exact (lhTopEquivOf L').symm_apply_apply _

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The Thom coordinates of the vector-bundle pair over a field**: across the bridge, then
Leray–Hirsch coordinates on the projectivisation pair. -/
def thomJmTotalOf (K : Type) [Field K] [CompactSpace X] [T2Space X] (p : Bundle X ι) {r : ℕ}
    {ξ : Hmod K (TopCat.of (Bundle.Proj p.plusOne)) 2}
    (L : LerayHirschGraded (projMapOf p.plusOne) ξ (r + 1)) :
    ↥(relCohomology K (TopCat.of (Bundle.Total p))
        ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p) (2 * r))
      →ₗ[K] ((i : Fin (r + 1)) → Hmod K (TopCat.of X) (2 * r - 2 * (i : ℕ))) :=
  (thomJmOf K (lhTopEquivOf L) (Set.range (Bundle.projIncl p))).comp
    (bridgeTotalOf K p (2 * r)).toLinearMap

theorem thomJmTotalOf_apply (K : Type) [Field K] [CompactSpace X] [T2Space X] (p : Bundle X ι)
    {r : ℕ} {ξ : Hmod K (TopCat.of (Bundle.Proj p.plusOne)) 2}
    (L : LerayHirschGraded (projMapOf p.plusOne) ξ (r + 1))
    (a : ↥(relCohomology K (TopCat.of (Bundle.Total p))
      ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p) (2 * r))) :
    thomJmTotalOf K p L a
      = thomJmOf K (lhTopEquivOf L) (Set.range (Bundle.projIncl p))
          (bridgeTotalOf K p (2 * r) a) := rfl

set_option maxHeartbeats 1000000 in
/-- **The Thom coordinates under a base restriction, over a field.**  Coordinate by
coordinate, the coordinates of the restricted class are the restrictions of the coordinates. -/
theorem thomJmTotal_restrictOf (K : Type) [Field K] [CompactSpace X] [T2Space X]
    (p : Bundle X ι) (U : Set X) [CompactSpace ↥U] [T2Space ↥U] {r : ℕ}
    {ξ : Hmod K (TopCat.of (Bundle.Proj p.plusOne)) 2}
    {ξ' : Hmod K (TopCat.of (Bundle.Proj (p.restrictTo U).plusOne)) 2}
    (hξ : pull (cmap (Bundle.projInclOn p.plusOne U)) 2 ξ = ξ')
    (L : LerayHirschGraded (projMapOf p.plusOne) ξ (r + 1))
    (L' : LerayHirschGraded (projMapOf ((p.restrictTo U).plusOne)) ξ' (r + 1))
    (x : ↥(relCohomology K (TopCat.of (Bundle.Total p))
      ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p) (2 * r))) :
    thomJmTotalOf K (p.restrictTo U) L'
        ((relPullback K (cmap (Bundle.totalInclOn p U))
          (totalInclOn_mapsTo p U) (2 * r)).hom x)
      = fun i : Fin (r + 1) => pull (inclSubtype U) (2 * r - 2 * (i : ℕ))
          (thomJmTotalOf K p L x i) :=
  ((thomJmTotalOf_apply K (p.restrictTo U) L'
        ((relPullback K (cmap (Bundle.totalInclOn p U))
          (totalInclOn_mapsTo p U) (2 * r)).hom x)).trans
      (congrArg
        (fun z => thomJmOf K (lhTopEquivOf L') (Set.range (Bundle.projIncl (p.restrictTo U))) z)
        (bridgeTotalRestrictOf K p U (2 * r) x).symm)).trans
    (thomJm_naturalOf L L' (cmap (Bundle.projInclOn p.plusOne U)) (inclSubtype U)
      (projInclOn_proj_square p U) hξ
      (fun z hz => projInclOn_range_mapsTo p U z hz)
      (bridgeTotalOf K p (2 * r) x))

/-! Audited on every build: `#audit_axioms` fails the build if a closure leaves the
classical allowlist. -/

#audit_axioms thomJm_naturalOf
#audit_axioms thomJmTotal_restrictOf

end ThomChernDeg

end

end GroupApproximation.CharClass
