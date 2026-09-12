import GroupApproximation.CharClass.MayerVietorisElementOf
import GroupApproximation.CharClass.KroneckerContractible
import GroupApproximation.CharClass.ThomPuncturedRecursion
import GroupApproximation.CharClass.ThomPuncturedSphere
import GroupApproximation.Meta.AxiomGuard

/-!
# The cohomology toolkit over a field, and the punctured-product recursion over `F_p`

Lane `lix-thom` of the stronger LIX programme (`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`
§1.5), successor of `sp-thom`.

`ThomToolkitInstance.lean` discharges the four fields of `CohomologyToolkit` at `F₂`.  This
file discharges `CohomologyToolkitOf K` at every field `K`, from the coefficient-generic
layers that now exist:

* **Mayer–Vietoris, vanishing form** — `mvExactXOf`, exactness of the Mayer–Vietoris sequence
  over a field at `H^{m+1}(X; K)`; the argument is the `F₂` one word for word;
* **homeomorphism and homotopy invariance** — `pullEquivOfHomotopyEquivOf`, a homeomorphism
  being a homotopy equivalence;
* **contractible spaces** — `cohomology_isZero_of_contractibleOf`.

`[Field K]` enters through Mayer–Vietoris and the contractible computation, both of which
dualise a quasi-isomorphism.

With the toolkit discharged, the punctured-product recursion and its base cases hold over
`K`.  This is the `hacyclic` hypothesis of Step C over `F_p`
(`ThomStepCEulerOf.topChernClass_ne_zero_of_su_ne_zero_naturalityOf`): a product of spheres
and projective spaces is top-punctured acyclic over `K`, once the Künneth factors of the
second coordinates are supplied.

## Main declarations

* `isZero_cohomology_of_coverOf` — Mayer–Vietoris, vanishing form, over a field.
* `thomCohProdContractibleOf` — a contractible factor is invisible to `H^*(−; K)`.
* `cohomologyToolkitOf` — **the toolkit over a field**.
* `puncturedAcyclic_prodOf`, `puncturedAcyclic_sphereOf` — the recursion and the sphere
  base case over a field.
* `kunnethFactor_of_contractibleOf`, `kunnethFactor_sphere_complOf` — the contractible and
  punctured-sphere Künneth factors, over any commutative ring.
-/

set_option autoImplicit false

open CategoryTheory Limits TopologicalSpace

namespace GroupApproximation.CharClass

noncomputable section

/-! ## 1. Mayer–Vietoris, vanishing form, over a field -/

/-- **Mayer–Vietoris, vanishing form, over a field.**  A class of `H^{m+1}(X; K)` restricting
to zero on both pieces comes from `H^m(U ∩ V; K)`, which is zero. -/
theorem isZero_cohomology_of_coverOf (K : Type) [Field K] {X : TopCat.{0}} (U V : Opens X)
    (hUV : U ⊔ V = ⊤) (m : ℕ)
    (hI : IsZero (Hmod K (mvInter U V) m))
    (hU : IsZero (Hmod K (mvU U) (m + 1)))
    (hV : IsZero (Hmod K (mvU V) (m + 1))) :
    IsZero (Hmod K X (m + 1)) := by
  haveI := ModuleCat.subsingleton_of_isZero hI
  haveI := ModuleCat.subsingleton_of_isZero hU
  haveI := ModuleCat.subsingleton_of_isZero hV
  have hsub : ∀ z : Hmod K X (m + 1), z = 0 := by
    intro z
    obtain ⟨w, hw⟩ := (mvExactXOf K U V hUV m z).1
      ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    rw [← hw, Subsingleton.elim w 0, map_zero]
  haveI : Subsingleton (Hmod K X (m + 1)) := ⟨fun a b => by rw [hsub a, hsub b]⟩
  exact ModuleCat.isZero_of_subsingleton _

/-! ## 2. The toolkit over a field -/

/-- A contractible factor disappears up to homotopy: `A × Y ≃ₕ A`. -/
def thomProdContractibleHomotopyEquiv (A Y : Type) [TopologicalSpace A] [TopologicalSpace Y]
    [ContractibleSpace Y] : ContinuousMap.HomotopyEquiv (A × Y) A :=
  ((ContinuousMap.HomotopyEquiv.refl A).prodCongr
      (ContractibleSpace.hequiv_unit Y).some).trans
    (Homeomorph.prodUnique A Unit).toHomotopyEquiv

/-- **A contractible factor is invisible to `H^*(−; K)`**, over any commutative ring: the
`K`-form of `cc-cohom-api`'s `cohProdContractible`, through `A × Y ≃ₕ A`. -/
def thomCohProdContractibleOf (K : Type) [CommRing K] (A Y : Type) [TopologicalSpace A]
    [TopologicalSpace Y] [ContractibleSpace Y] (n : ℕ) :
    Hmod K (TopCat.of A) n ≃ₗ[K] Hmod K (TopCat.of (A × Y)) n :=
  pullEquivOfHomotopyEquivOf K (thomProdContractibleHomotopyEquiv A Y) n

/-- **The cohomology toolkit of the punctured-product recursion, over a field.** -/
theorem cohomologyToolkitOf (K : Type) [Field K] : CohomologyToolkitOf K :=
  ⟨fun Z _ U V hUV m hI hU hV =>
      isZero_cohomology_of_coverOf K (X := TopCat.of Z) U V hUV m hI hU hV,
   fun _ _ _ _ e n h =>
      thomIsZero_of_linearEquiv (pullEquivOfHomotopyEquivOf K e.toHomotopyEquiv n).symm h,
   fun _ _ _ _ e n h => thomIsZero_of_linearEquiv (pullEquivOfHomotopyEquivOf K e n).symm h,
   fun A _ hc n hn => by
     haveI := hc
     exact cohomology_isZero_of_contractibleOf K A n hn⟩

/-! ## 3. The recursion over a field -/

/-- **The punctured-product recursion over a field**, with the toolkit discharged. -/
theorem puncturedAcyclic_prodOf {K : Type} [Field K] {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [T1Space X] [T1Space Y] {dX dY : ℕ} {x₀ : X} {y₀ : Y}
    (kY : KunnethFactorOf K Y dY) (kY' : KunnethFactorOf K ↥({y₀}ᶜ : Set Y) (dY - 1))
    (hX : PuncturedAcyclicOf K X dX x₀) (hY : PuncturedAcyclicOf K Y dY y₀) :
    PuncturedAcyclicOf K (X × Y) (dX + dY) (x₀, y₀) :=
  PuncturedAcyclicOf.prod (cohomologyToolkitOf K) kY kY' hX hY

/-- **The sphere base case over a field.**  The puncture is contractible by stereographic
projection; the remaining input is the vanishing of `H^k(S^n; K)` above `n`. -/
theorem puncturedAcyclic_sphereOf {K : Type} [Field K] {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {n : ℕ} (hn : 0 < n) (v : Metric.sphere (0 : E) 1)
    (hvanish : ∀ k, n < k → IsZero (Hmod K (TopCat.of ↥(Metric.sphere (0 : E) 1)) k)) :
    PuncturedAcyclicOf K ↥(Metric.sphere (0 : E) 1) n v :=
  puncturedAcyclic_of_contractible (cohomologyToolkitOf K) hn hvanish
    (contractibleSpace_sphere_compl v)

/-- **A contractible factor is a Künneth factor of dimension zero**, over any commutative
ring; no Künneth theorem is involved. -/
theorem kunnethFactor_of_contractibleOf (K : Type) [CommRing K] (Y : Type) [TopologicalSpace Y]
    [ContractibleSpace Y] : KunnethFactorOf K Y 0 :=
  kunnethFactor_of_prodEquiv Y (fun A _ n => thomCohProdContractibleOf K A Y n)

/-- **A punctured sphere is a Künneth factor of any dimension**, over any commutative ring. -/
theorem kunnethFactor_sphere_complOf (K : Type) [CommRing K] {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v : Metric.sphere (0 : E) 1) (q : ℕ) :
    KunnethFactorOf K ↥({v}ᶜ : Set ↥(Metric.sphere (0 : E) 1)) q :=
  (kunnethFactor_of_contractibleOf K _).mono (Nat.zero_le q)

/-! Audited on every build: `#audit_axioms` fails the build if a closure leaves the
classical allowlist. -/

#audit_axioms isZero_cohomology_of_coverOf
#audit_axioms cohomologyToolkitOf
#audit_axioms puncturedAcyclic_prodOf
#audit_axioms puncturedAcyclic_sphereOf
#audit_axioms kunnethFactor_sphere_complOf

end

end GroupApproximation.CharClass
