import GroupApproximation.CharClass.ThomBridgeTotal
import GroupApproximation.CharClass.ThomHabsOf
import GroupApproximation.CharClass.RelativeSubspaceIsoOf
import GroupApproximation.CharClass.KroneckerContractible
import GroupApproximation.Meta.AxiomGuard

/-!
# The Thom bridge and the Thom data of the vector-bundle pair, over a field

Lane `lix-thom` of the stronger LIX programme (`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`
§1.5), successor of `sp-thom`.

At `F₂`, `ThomBridgeTotal.lean` carries the degreewise Thom data of the projectivisation
pair `(P(p ⊕ 1), P(p))` across the Thom bridge to the vector-bundle pair `(E, E ∖ 0)`, where
the odd side of Step C needs it.  The bridge has three steps: excision to the affine chart,
the chart identified with the total space (`bridgeChartOf K`), and the punctured
projectivisation replaced by the hyperplane at infinity (`bridgeHyperplaneOf K`).  The last
step rests on one topological input, that the hyperplane inclusion is an isomorphism on
cohomology, and that is homotopy invariance (`pullEquivOfHomotopyEquivOf K`).

Over a field `K` every step has its `K`-form, so the transport goes through verbatim.  The
Leray–Hirsch generator of the projectivisation is left as an arbitrary class
`ξ : H²(P(p ⊕ 1); K)` rather than fixed to a tautological Euler class: over `K` the
Grothendieck relation is stated with the dual tautological class (`lix-lh`), and nothing
here depends on which class is used.

## Main declarations

* `hyperplane_hsubOf`, `bridgeHyperplaneOf` — step three over `K`.
* `bridgeTotalOf` — **the Thom bridge over a field**.
* `thomData_transportOf` — the algebra, over any commutative ring.
* `thomData_total_of_lerayHirschOf` — **the degreewise Thom data of the vector-bundle pair
  over a field**.
-/

set_option autoImplicit false

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace ThomChernDeg

open LH

set_option linter.unusedSectionVars false

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## 1. Step three over `K` -/

/-- **The hyperplane inclusion is an isomorphism on `K`-cohomology.**  It is the homotopy
inverse of `cc-bundle`'s equivalence composed with a homeomorphism. -/
theorem hyperplane_hsubOf (K : Type) [CommRing K] [CompactSpace X] [T2Space X]
    (p : Bundle X ι) (k : ℕ) :
    Function.Bijective (pull (K := K) (subInclusion (range_projIncl_subset_notZero p)) k) := by
  have hcomp : ∀ a, pull (cmap (Bundle.projInclHomeoRange p).toHomotopyEquiv.toFun) k
      (pull (K := K) (subInclusion (range_projIncl_subset_notZero p)) k a)
      = pull (cmap (Bundle.notZeroOpensHomotopyEquivProj p).symm.toFun) k a := by
    intro a
    rw [← pull_comp]
    exact congrArg (fun f => pull f k a) (incl_comp_eq_invFun p)
  have hhomeo :=
    (pullEquivOfHomotopyEquivOf K (Bundle.projInclHomeoRange p).toHomotopyEquiv k).bijective
  have hinv :=
    (pullEquivOfHomotopyEquivOf K (Bundle.notZeroOpensHomotopyEquivProj p).symm k).bijective
  constructor
  · intro a b hab
    have h1 := congrArg (pull (cmap (Bundle.projInclHomeoRange p).toHomotopyEquiv.toFun) k) hab
    rw [hcomp, hcomp] at h1
    exact hinv.1 h1
  · intro b
    obtain ⟨a, ha⟩ :=
      hinv.2 (pull (cmap (Bundle.projInclHomeoRange p).toHomotopyEquiv.toFun) k b)
    refine ⟨a, hhomeo.1 ?_⟩
    show pull (cmap (Bundle.projInclHomeoRange p).toHomotopyEquiv.toFun) k
        (pull (subInclusion (range_projIncl_subset_notZero p)) k a)
      = pull (cmap (Bundle.projInclHomeoRange p).toHomotopyEquiv.toFun) k b
    rw [hcomp]
    exact ha

/-- **Step three of the Thom bridge over `K`.** -/
theorem bridgeHyperplaneOf (K : Type) [CommRing K] (p : Bundle X ι)
    (hsub : ∀ k : ℕ,
      Function.Bijective (pull (K := K) (subInclusion (range_projIncl_subset_notZero p)) k))
    (n : ℕ) :
    Function.Bijective
      (relPullback K (𝟙 (TopCat.of (Bundle.Proj p.plusOne)))
        (fun _ hx => range_projIncl_subset_notZero p hx) n).hom :=
  RelativeSupport.relPullback_id_bijective_of_subspace_isoOf K
    (range_projIncl_subset_notZero p) hsub n

/-! ## 2. The composite bridge over a field -/

/-- **The Thom bridge over a field.**  The relative group of the vector-bundle pair is the
relative group of the projectivisation pair, in every degree. -/
def bridgeTotalOf (K : Type) [Field K] [CompactSpace X] [T2Space X] (p : Bundle X ι)
    (n : ℕ) :
    ↥(relCohomology K (TopCat.of (Bundle.Total p))
        ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p) n)
      ≃ₗ[K] ↥(relCohomology K (TopCat.of (Bundle.Proj p.plusOne))
        (Set.range (Bundle.projIncl p)) n) :=
  LinearEquiv.trans (bridgeChartOf K p n).symm.toLinearEquiv
    (LinearEquiv.ofBijective
      (relPullback K (𝟙 (TopCat.of (Bundle.Proj p.plusOne)))
        (fun _ hx => range_projIncl_subset_notZero p hx) n).hom
      (bridgeHyperplaneOf K p (hyperplane_hsubOf K p) n))

/-! ## 3. Moving the data across an equivalence -/

/-- **An injective map with a prescribed range stays one after precomposition with an
equivalence**, over any commutative ring. -/
theorem thomData_transportOf {K : Type} [CommRing K] {A A' N : Type}
    [AddCommGroup A] [Module K A] [AddCommGroup A'] [Module K A']
    [AddCommGroup N] [Module K N]
    (φ : A ≃ₗ[K] A') (jm : A' →ₗ[K] N) (hinj : Function.Injective jm)
    {S : Submodule K N} (hrange : LinearMap.range jm = S) :
    ∃ (jm0 : A →ₗ[K] N) (_ : Function.Injective jm0), LinearMap.range jm0 = S := by
  refine ⟨jm.comp φ.toLinearMap, hinj.comp φ.injective, ?_⟩
  rw [← hrange]
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨φ a, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨φ.symm b, congrArg jm (φ.apply_symm_apply b)⟩

/-! ## 4. The Thom data where the odd side needs it -/

/-- **The degreewise Thom data of the vector-bundle pair over a field.**  The
projectivisation's data over `K`, carried across the bridge.  The generator `ξ` of the
ambient Leray–Hirsch instance is any degree-two class. -/
theorem thomData_total_of_lerayHirschOf (K : Type) [Field K] [CompactSpace X] [T2Space X]
    (p : Bundle X ι)
    (π' : TopCat.of (Set.range (Bundle.projIncl p)) ⟶ TopCat.of X)
    (hπ : sInclusion (Set.range (Bundle.projIncl p)) ≫ projMapOf p.plusOne = π')
    (ξ : Hmod K (TopCat.of (Bundle.Proj p.plusOne)) 2)
    (ξ' : Hmod K (TopCat.of (Set.range (Bundle.projIncl p))) 2)
    (hξ : pull (sInclusion (Set.range (Bundle.projIncl p))) 2 ξ = ξ')
    {r : ℕ} (hr : 1 ≤ r)
    (L : LerayHirschGraded (projMapOf p.plusOne) ξ (r + 1))
    (L' : LerayHirschGraded π' ξ' r) :
    ∃ (jm : ↥(relCohomology K (TopCat.of (Bundle.Total p))
          ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p)
          (2 * r))
        →ₗ[K] ((i : Fin (r + 1)) → Hmod K (TopCat.of X) (2 * r - 2 * (i : ℕ))))
      (_ : Function.Injective jm),
      LinearMap.range jm = LinearMap.ker (ThomDeg.restrictMap (R := K)
        (M := fun i : Fin (r + 1) => Hmod K (TopCat.of X) (2 * r - 2 * (i : ℕ)))
        (fun i => chernMulOf L' i)) := by
  obtain ⟨jm, hinj, hrange⟩ :=
    thomData_of_lerayHirschOf (X := TopCat.of X)
      (P := TopCat.of (Bundle.Proj p.plusOne)) (r := r)
      (Set.range (Bundle.projIncl p)) (projMapOf p.plusOne)
      π' hπ ξ ξ' hξ hr L L'
  exact thomData_transportOf (bridgeTotalOf K p (2 * r)) jm hinj hrange

/-! Audited on every build: `#audit_axioms` fails the build if a closure leaves the
classical allowlist. -/

#audit_axioms hyperplane_hsubOf
#audit_axioms thomData_total_of_lerayHirschOf

end ThomChernDeg

end

end GroupApproximation.CharClass
