import GroupApproximation.CharClass.ThomTopLineCircle
import GroupApproximation.CharClass.ThomKunnethOf
import GroupApproximation.CharClass.KroneckerSphere
import GroupApproximation.CharClass.MayerVietorisDisjointOf
import GroupApproximation.CharClass.CohomologyKunnethHemiOf
import GroupApproximation.CharClass.CohomologyKunnethSplitOf
import GroupApproximation.Meta.AxiomGuard

/-!
# Top lines of products of spheres and projective spaces, over a field

Lane `lix-thom` of the stronger LIX programme (`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`
§1.5), successor of `sp-thom`.

Step C needs the top cohomology of the base `N` to be a line (`absLine`) and nothing above it
(the vanishing half of `hacyclic`).  At `F₂` that is `ThomTopLine.HasTopLine`, propagated
through products with spheres and `ℂP^d` by one Mayer–Vietoris connecting isomorphism, plus
the circle step of `ThomTopLineCircle`, where the cover of `S¹` has disconnected
intersection and a rank count replaces the isomorphism.

Over a field `K` every ingredient has its `K`-form: the sphere computation
(`KroneckerSphere`), the connecting isomorphism (`mvConnectingIsoOf`), the splitting of a
disjoint cover (`mvPairEquivOf`), and the band of `A × S¹` (`CohomologyKunnethHemiOf`).  The
rank count in the circle step is dimension theory over a field and needs nothing else.  So
the whole propagation runs over `K`, and the circle step is a theorem here, not a hypothesis.

## Main declarations

* `HasTopLineOf` — no `K`-cohomology above degree `d`, and a line in degree `d`.
* `hasTopLineOf_sphere` — the base case.
* `prodCoverConnectingOf` — the single Mayer–Vietoris move over `K`.
* `hasTopLineOf_prod_circle` — **the circle step over a field**.
* `hasTopLineOf_prod_sphere`, `hasTopLineOf_prod_CP` — crossing with `S^n`, `n ≥ 1`, and with
  `ℂP^d`, `d ≥ 1`, raises the top degree by `n` and by `2d`.
-/

set_option autoImplicit false

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

/-! ## 1. The predicate -/

/-- **A space with a top line over `K`.**  No `K`-cohomology strictly above degree `d`, and
the degree-`d` cohomology is a line. -/
structure HasTopLineOf (K : Type) [CommRing K] (Z : Type) [TopologicalSpace Z] (d : ℕ) :
    Prop where
  /-- No cohomology strictly above the top degree. -/
  vanish : ∀ k, d < k → IsZero (Hmod K (TopCat.of Z) k)
  /-- The top cohomology is a line over `K`. -/
  line : Nonempty (Hmod K (TopCat.of Z) d ≃ₗ[K] K)

/-- A top line transports along a homotopy equivalence. -/
theorem HasTopLineOf.congrHomotopy {K : Type} [CommRing K] {Z W : Type} [TopologicalSpace Z]
    [TopologicalSpace W] {d : ℕ} (h : HasTopLineOf K Z d)
    (e : ContinuousMap.HomotopyEquiv Z W) : HasTopLineOf K W d := by
  obtain ⟨l⟩ := h.line
  exact ⟨fun k hk => thomIsZero_of_linearEquiv (pullEquivOfHomotopyEquivOf K e k) (h.vanish k hk),
    ⟨(pullEquivOfHomotopyEquivOf K e d).trans l⟩⟩

/-- A top line transports along a homeomorphism. -/
theorem HasTopLineOf.congr {K : Type} [CommRing K] {Z W : Type} [TopologicalSpace Z]
    [TopologicalSpace W] {d : ℕ} (h : HasTopLineOf K Z d) (e : Z ≃ₜ W) : HasTopLineOf K W d :=
  h.congrHomotopy e.toHomotopyEquiv

/-- **`H^n(Sⁿ; K) ≃ K`, with nothing above**, over a field. -/
theorem hasTopLineOf_sphere (K : Type) [Field K] (n : ℕ) (hn : 1 ≤ n) :
    HasTopLineOf K (Sphere n) n :=
  ⟨fun k hk => sphere_coh_isZero_of_gtOf K n k hk, ⟨sphereTopEquivOf K n hn⟩⟩

/-! ## 2. The single Mayer–Vietoris move -/

/-- Cohomology transported along an equality of subsets, over any commutative ring. -/
def cohSetCongrOf (K : Type) [CommRing K] {Y : Type} [TopologicalSpace Y] {S T : Set Y}
    (h : S = T) (k : ℕ) : Hmod K (TopCat.of ↥S) k ≃ₗ[K] Hmod K (TopCat.of ↥T) k :=
  (pullEquivOfHomotopyEquivOf K (Homeomorph.setCongr h).toHomotopyEquiv k).symm

/-- **The Mayer–Vietoris connecting isomorphism of a product cover, over a field.**  Cross a
two-set open cover `Y = U ∪ V` with `A`; if `A × U` and `A × V` have no `K`-cohomology in
degrees `m` and `m+1`, then `H^m(A × W; K) ≅ H^{m+1}(A × Y; K)` for any `U ∩ V ≃ W`. -/
def prodCoverConnectingOf (K : Type) [Field K] (A : Type) [TopologicalSpace A] {Y : Type}
    [TopologicalSpace Y] (U V : Opens Y) (hUV : U ⊔ V = ⊤) {W : Type} [TopologicalSpace W]
    (eW : ContinuousMap.HomotopyEquiv ↥((U ⊓ V : Opens Y) : Set Y) W) (m : ℕ)
    (hU : IsZero (Hmod K (TopCat.of ↥((prodOpen A U : Opens (A × Y)) : Set (A × Y))) m))
    (hV : IsZero (Hmod K (TopCat.of ↥((prodOpen A V : Opens (A × Y)) : Set (A × Y))) m))
    (hU' : IsZero (Hmod K (TopCat.of ↥((prodOpen A U : Opens (A × Y)) : Set (A × Y))) (m + 1)))
    (hV' : IsZero (Hmod K (TopCat.of ↥((prodOpen A V : Opens (A × Y)) : Set (A × Y))) (m + 1))) :
    Hmod K (TopCat.of (A × W)) m ≃ₗ[K] Hmod K (TopCat.of (A × Y)) (m + 1) :=
  ((pullEquivOfHomotopyEquivOf K ((ContinuousMap.HomotopyEquiv.refl A).prodCongr eW) m).trans
      ((prodOpenCohEquivOf K A (U ⊓ V) m).trans
        (cohSetCongrOf K
          (S := ((prodOpen A (U ⊓ V) : Opens (A × Y)) : Set (A × Y)))
          (T := ((prodOpen A U : Opens (A × Y)) : Set (A × Y))
            ∩ ((prodOpen A V : Opens (A × Y)) : Set (A × Y)))
          (by rw [← prodOpen_inf A U V, Opens.coe_inf]) m))).trans
    (mvConnectingIsoOf K (X := TopCat.of (A × Y)) (prodOpen A U) (prodOpen A V)
      (prodOpen_sup A hUV) m hU hV hU' hV').toLinearEquiv

/-! ## 3. The sphere step -/

set_option maxHeartbeats 1000000 in
/-- **The sphere step over a field.**  Crossing with `S^{n+1}` raises the top degree by
`n+1`, provided `n ≥ 1`. -/
theorem hasTopLineOf_prod_sphere_succ (K : Type) [Field K] (A : Type) [TopologicalSpace A]
    (p n : ℕ) (hn : 1 ≤ n) (hA : HasTopLineOf K A p)
    (hAn : HasTopLineOf K (A × Sphere n) (p + n)) :
    HasTopLineOf K (A × Sphere (n + 1)) (p + (n + 1)) := by
  obtain ⟨l⟩ := hAn.line
  refine ⟨fun k hk => (kunnethFactor_sphereOf K (n + 1)).prod A p hA.vanish k (by omega), ⟨?_⟩⟩
  have hU : IsZero (Hmod K (TopCat.of
      ↥((prodOpen A (upperOpens n) : Opens (A × Sphere (n + 1))) : Set (A × Sphere (n + 1))))
      (p + n)) :=
    isZero_prodOpen_of_contractibleOf K A (upperOpens n) (p + n) (hA.vanish (p + n) (by omega))
  have hV : IsZero (Hmod K (TopCat.of
      ↥((prodOpen A (lowerOpens n) : Opens (A × Sphere (n + 1))) : Set (A × Sphere (n + 1))))
      (p + n)) :=
    isZero_prodOpen_of_contractibleOf K A (lowerOpens n) (p + n) (hA.vanish (p + n) (by omega))
  have hU' : IsZero (Hmod K (TopCat.of
      ↥((prodOpen A (upperOpens n) : Opens (A × Sphere (n + 1))) : Set (A × Sphere (n + 1))))
      (p + n + 1)) :=
    isZero_prodOpen_of_contractibleOf K A (upperOpens n) (p + n + 1)
      (hA.vanish (p + n + 1) (by omega))
  have hV' : IsZero (Hmod K (TopCat.of
      ↥((prodOpen A (lowerOpens n) : Opens (A × Sphere (n + 1))) : Set (A × Sphere (n + 1))))
      (p + n + 1)) :=
    isZero_prodOpen_of_contractibleOf K A (lowerOpens n) (p + n + 1)
      (hA.vanish (p + n + 1) (by omega))
  exact (prodCoverConnectingOf K A (Y := Sphere (n + 1)) (upperOpens n) (lowerOpens n)
    (upperOpens_sup_lowerOpens n) (bandInterHomotopyEquiv n) (p + n)
    hU hV hU' hV').symm.trans l

/-! ## 4. The circle step -/

section Circle

variable (K : Type) [Field K] (A : Type) [TopologicalSpace A] (p : ℕ)

/-- The positive half of `A × S⁰` has the `K`-cohomology of `A`. -/
def szPosProdCohOf (k : ℕ) :
    Hmod K (TopCat.of A) k ≃ₗ[K] Hmod K (mvU (szPosProd A)) k :=
  (cohProdContractibleOf K A ↥((sphereZeroPos : Opens (Sphere 0)) : Set (Sphere 0)) k).trans
    (prodOpenCohEquivOf K A sphereZeroPos k)

/-- The negative half of `A × S⁰` has the `K`-cohomology of `A`. -/
def szNegProdCohOf (k : ℕ) :
    Hmod K (TopCat.of A) k ≃ₗ[K] Hmod K (mvU (szNegProd A)) k :=
  (cohProdContractibleOf K A ↥((sphereZeroNeg : Opens (Sphere 0)) : Set (Sphere 0)) k).trans
    (prodOpenCohEquivOf K A sphereZeroNeg k)

/-- **`H^k(A × S⁰; K) ≅ H^k(A; K)²`.** -/
def sphereZeroProdEquivOf (k : ℕ) :
    Hmod K (TopCat.of (A × Sphere 0)) k ≃ₗ[K] (Hmod K (TopCat.of A) k × Hmod K (TopCat.of A) k) :=
  (mvPairEquivOf K (szPosProd A) (szNegProd A) (szProd_sup A) k).trans
    ((szPosProdCohOf K A k).symm.prodCongr (szNegProdCohOf K A k).symm)

/-- `H^p(A × S⁰; K)` is two dimensional when `A` has a top line in degree `p`. -/
theorem finrank_prod_sphereZeroOf (hA : HasTopLineOf K A p) :
    Module.finrank K (Hmod K (TopCat.of (A × Sphere 0)) p) = 2 := by
  obtain ⟨l⟩ := hA.line
  rw [(sphereZeroProdEquivOf K A p).finrank_eq, (l.prodCongr l).finrank_eq,
    Module.finrank_prod, Module.finrank_self]

/-- The band of `A × S¹` is `A × S⁰`, so it too is two dimensional. -/
theorem finrank_band_circleOf (hA : HasTopLineOf K A p) :
    Module.finrank K (Hmod K (TopCat.of ↥(KnHemi.bandSet A 0)) p) = 2 := by
  rw [← (KnHemi.bandPullEquivOf K A 0 p).finrank_eq]
  exact finrank_prod_sphereZeroOf K A p hA

/-- **A slice retracts the projection**, so pulling back from `A` to the band of `A × S¹` is
injective over `K`. -/
theorem pullLinear_prSub_band_injectiveOf (k : ℕ) :
    Function.Injective (pullLinear (K := K) (KnHemi.prSub A 0 (KnHemi.bandSet A 0)) k) := by
  obtain ⟨s⟩ := nonempty_sphereZeroPos
  intro u u' h
  have h2 : pull (cmap (KnHemi.bandHomotopyEquiv A 0).toFun) k (pull (knPrY A 0) k u)
      = pull (cmap (KnHemi.bandHomotopyEquiv A 0).toFun) k (pull (knPrY A 0) k u') := by
    rw [KnHemi.pull_bandHE_knPrYOf, KnHemi.pull_bandHE_knPrYOf]
    exact h
  exact pull_knPrY_injectiveOf K A 0 (s : Sphere 0) k (KnHemi.pull_bandHE_injectiveOf K A 0 k h2)

set_option maxHeartbeats 1000000 in
/-- **The kernel of the connecting map is exactly the image of `pr_A^*`**, over a field. -/
theorem ker_mvDelta_circleOf :
    LinearMap.ker (mvDeltaOf K (KnHemi.hemiU A 0) (KnHemi.hemiV A 0) (KnHemi.hemi_sup A 0) p).hom
      = LinearMap.range (pullLinear (K := K) (KnHemi.prSub A 0 (KnHemi.bandSet A 0)) p) := by
  apply le_antisymm
  · intro w hw
    rw [LinearMap.mem_ker] at hw
    obtain ⟨a, b, hab⟩ :=
      (mvExactWOf K (KnHemi.hemiU A 0) (KnHemi.hemiV A 0) (KnHemi.hemi_sup A 0) p w).1 hw
    obtain ⟨c, hc⟩ := KnHemi.exists_pull_prSub_of_resOf K A 0 p w a b hab
    exact ⟨c, hc⟩
  · rintro w ⟨c, rfl⟩
    rw [LinearMap.mem_ker]
    refine (mvExactWOf K (KnHemi.hemiU A 0) (KnHemi.hemiV A 0) (KnHemi.hemi_sup A 0) p _).2
      ⟨pull (KnHemi.prSub A 0 (KnHemi.hemiUSet A 0)) p c, 0, ?_⟩
    show (mvResWUOf K (KnHemi.hemiU A 0) (KnHemi.hemiV A 0) (KnHemi.hemi_sup A 0) p).hom
          (pull (KnHemi.prSub A 0 (KnHemi.hemiUSet A 0)) p c)
        + (mvResWVOf K (KnHemi.hemiU A 0) (KnHemi.hemiV A 0) (KnHemi.hemi_sup A 0) p).hom 0
        = pull (KnHemi.prSub A 0 (KnHemi.bandSet A 0)) p c
    rw [KnHemi.mvResWUOf_pull_prSub, map_zero, add_zero]

set_option maxHeartbeats 1000000 in
/-- **The circle step over a field.**  If the `K`-cohomology of `A` is a line in its top
degree `p`, then that of `A × S¹` is a line in degree `p + 1`. -/
theorem hasTopLineOf_prod_circle (hA : HasTopLineOf K A p) :
    HasTopLineOf K (A × Sphere 1) (p + 1) := by
  have hUz : IsZero (Hmod K (mvU (KnHemi.hemiU A 0)) (p + 1)) :=
    isZero_prodOpen_of_contractibleOf K A (upperOpens 0) (p + 1) (hA.vanish (p + 1) (by omega))
  have hVz : IsZero (Hmod K (mvU (KnHemi.hemiV A 0)) (p + 1)) :=
    isZero_prodOpen_of_contractibleOf K A (lowerOpens 0) (p + 1) (hA.vanish (p + 1) (by omega))
  haveI := ModuleCat.subsingleton_of_isZero hUz
  haveI := ModuleCat.subsingleton_of_isZero hVz
  have hsurj : Function.Surjective
      (mvDeltaOf K (KnHemi.hemiU A 0) (KnHemi.hemiV A 0) (KnHemi.hemi_sup A 0) p).hom := by
    intro x
    exact (mvExactXOf K (KnHemi.hemiU A 0) (KnHemi.hemiV A 0) (KnHemi.hemi_sup A 0) p x).1
      ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  haveI : Module.Finite K (Hmod K (TopCat.of ↥(KnHemi.bandSet A 0)) p) :=
    Module.finite_of_finrank_pos (by rw [finrank_band_circleOf K A p hA]; omega)
  have hrn := LinearMap.finrank_range_add_finrank_ker
    (mvDeltaOf K (KnHemi.hemiU A 0) (KnHemi.hemiV A 0) (KnHemi.hemi_sup A 0) p).hom
  have hkerrank : Module.finrank K
      (LinearMap.ker (mvDeltaOf K (KnHemi.hemiU A 0) (KnHemi.hemiV A 0)
        (KnHemi.hemi_sup A 0) p).hom) = 1 := by
    obtain ⟨l⟩ := hA.line
    rw [ker_mvDelta_circleOf K A p,
      LinearMap.finrank_range_of_inj (pullLinear_prSub_band_injectiveOf K A p), l.finrank_eq,
      Module.finrank_self]
  have hrangerank : Module.finrank K
      (LinearMap.range (mvDeltaOf K (KnHemi.hemiU A 0) (KnHemi.hemiV A 0)
        (KnHemi.hemi_sup A 0) p).hom)
      = Module.finrank K (Hmod K (TopCat.of (A × Sphere 1)) (p + 1)) :=
    (LinearEquiv.ofTop _ (LinearMap.range_eq_top.2 hsurj)).finrank_eq
  have hfin : Module.finrank K (Hmod K (TopCat.of (A × Sphere 1)) (p + 1)) = 1 := by
    rw [hkerrank, finrank_band_circleOf K A p hA, hrangerank] at hrn
    omega
  haveI : Module.Finite K (Hmod K (TopCat.of (A × Sphere 1)) (p + 1)) :=
    Module.finite_of_finrank_pos (by rw [hfin]; omega)
  refine ⟨fun k hk => (kunnethFactor_sphereOf K 1).prod A p hA.vanish k (by omega), ⟨?_⟩⟩
  exact LinearEquiv.ofFinrankEq _ _ (by rw [hfin, Module.finrank_self])

end Circle

/-! ## 5. The sphere induction -/

/-- **The sphere induction over a field.**  Crossing with any sphere of positive dimension
raises the top degree by that dimension. -/
theorem hasTopLineOf_prod_sphere (K : Type) [Field K] (A : Type) [TopologicalSpace A] (p : ℕ)
    (hA : HasTopLineOf K A p) : ∀ n, 1 ≤ n → HasTopLineOf K (A × Sphere n) (p + n) := by
  intro n
  induction n with
  | zero => intro hn; exact absurd hn (by omega)
  | succ n ih =>
      intro _
      rcases Nat.eq_zero_or_pos n with hz | hpos
      · subst hz
        exact hasTopLineOf_prod_circle K A p hA
      · exact hasTopLineOf_prod_sphere_succ K A p n hpos hA (ih hpos)

/-! ## 6. The projective induction -/

set_option maxHeartbeats 1000000 in
/-- **The projective step over a field.**  Crossing with `ℂP^{d+1}` raises the top degree by
`2(d+1)`, the input being the top line of `A × S^{2d+1}`. -/
theorem hasTopLineOf_prod_CP_succ (K : Type) [Field K] (A : Type) [TopologicalSpace A]
    (p d : ℕ) (hA : HasTopLineOf K A p)
    (hS : HasTopLineOf K (A × Sphere (2 * d + 1)) (p + (2 * d + 1))) :
    HasTopLineOf K (A × CP (d + 1)) (p + 2 * (d + 1)) := by
  obtain ⟨l⟩ := hS.line
  haveI := contractibleSpace_chartOpen d
  refine ⟨fun k hk => (kunnethFactor_CPOf K (d + 1)).prod A p hA.vanish k (by omega), ⟨?_⟩⟩
  have hU : IsZero (Hmod K (TopCat.of
      ↥((prodOpen A (chartOpen d) : Opens (A × CP (d + 1))) : Set (A × CP (d + 1))))
      (p + 2 * d + 1)) :=
    isZero_prodOpen_of_contractibleOf K A (chartOpen d) (p + 2 * d + 1)
      (hA.vanish (p + 2 * d + 1) (by omega))
  have hU' : IsZero (Hmod K (TopCat.of
      ↥((prodOpen A (chartOpen d) : Opens (A × CP (d + 1))) : Set (A × CP (d + 1))))
      (p + 2 * d + 1 + 1)) :=
    isZero_prodOpen_of_contractibleOf K A (chartOpen d) (p + 2 * d + 1 + 1)
      (hA.vanish (p + 2 * d + 1 + 1) (by omega))
  have hV : IsZero (Hmod K (TopCat.of
      ↥((prodOpen A (punctOpen d) : Opens (A × CP (d + 1))) : Set (A × CP (d + 1))))
      (p + 2 * d + 1)) :=
    isZero_prodOpen_of_homotopyEquivOf K A (punctOpen d) (punctOpenHomotopyEquiv d)
      (p + 2 * d + 1) ((kunnethFactor_CPOf K d).prod A p hA.vanish (p + 2 * d + 1) (by omega))
  have hV' : IsZero (Hmod K (TopCat.of
      ↥((prodOpen A (punctOpen d) : Opens (A × CP (d + 1))) : Set (A × CP (d + 1))))
      (p + 2 * d + 1 + 1)) :=
    isZero_prodOpen_of_homotopyEquivOf K A (punctOpen d) (punctOpenHomotopyEquiv d)
      (p + 2 * d + 1 + 1)
      ((kunnethFactor_CPOf K d).prod A p hA.vanish (p + 2 * d + 1 + 1) (by omega))
  exact (prodCoverConnectingOf K A (Y := CP (d + 1)) (chartOpen d) (punctOpen d)
    (chartOpen_sup_punctOpen d) (interSphereHomotopyEquiv d) (p + 2 * d + 1)
    hU hV hU' hV').symm.trans l

/-- **The projective induction over a field.**  Crossing with `ℂP^d`, `d ≥ 1`, raises the top
degree by `2d`. -/
theorem hasTopLineOf_prod_CP (K : Type) [Field K] (A : Type) [TopologicalSpace A] (p : ℕ)
    (hA : HasTopLineOf K A p) : ∀ d, 1 ≤ d → HasTopLineOf K (A × CP d) (p + 2 * d) := by
  intro d
  induction d with
  | zero => intro hd; exact absurd hd (by omega)
  | succ d _ih =>
      intro _
      exact hasTopLineOf_prod_CP_succ K A p d hA
        (hasTopLineOf_prod_sphere K A p hA (2 * d + 1) (by omega))

/-! Audited on every build: `#audit_axioms` fails the build if a closure leaves the
classical allowlist. -/

#audit_axioms hasTopLineOf_prod_circle
#audit_axioms hasTopLineOf_prod_sphere
#audit_axioms hasTopLineOf_prod_CP

end

end GroupApproximation.CharClass
