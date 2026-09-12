import GroupApproximation.CharClass.RelativeSubspaceIsoOf
import GroupApproximation.CharClass.RelativeProdContractible
import GroupApproximation.CharClass.KroneckerContractible
import GroupApproximation.Meta.AxiomGuard

/-!
# The relative group of a product pair over a contractible base, over any ring

Lane `lix-coeff` of the STW Problem LIX strengthening
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.5).

Additive twin of `RelativeProdContractible.lean` with the coefficient ring a parameter.  The
`F₂` file takes its two absolute bijectivity inputs from `CohomologyBridge`'s
`pullEquivOfHomotopyEquiv`, which is pinned at `ZMod 2`; the generic
`KroneckerContractible.pullEquivOfHomotopyEquivOf` (homotopy invariance over any
commutative ring) replaces it, and the five lemma is `relPullback_bijective_of_absoluteOf`.
No field is needed anywhere: `[CommRing K]` throughout.

The maps (`sliceMap`, `sndMap`, `subSndCMap`, `slice_comp_snd`, `subSlice_comp_subSnd`) and the
homotopy equivalences (`prodSndHomotopyEquiv`, `subSndHomotopyEquiv`) are the `F₂` file's own,
reused: they carry no coefficients.

## Main results

* `relPullback_slice_bijectiveOf` — the slice induces a bijection on `H^{n+1}(−, −; K)`.
* `relCohomologyProdIsoGenOf`, `relCohomologyProdIsoOf` — the bundled isomorphisms, with
  their underlying maps named by `_hom` lemmas.
-/

open CategoryTheory Limits AlgebraicTopology
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

namespace RelativeSupport

noncomputable section

variable {B E : Type} [TopologicalSpace B] [TopologicalSpace E]

/-! ## 1. Functoriality of the ambient pullback over `K` -/

theorem absPull_compOf (K : Type) [CommRing K] {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (m : ℕ) : absPullOf K (f ≫ g) m = absPullOf K g m ≫ absPullOf K f m := by
  show HomologicalComplex.homologyMap
    ((singularCochainComplexFunctor K (ModuleCat.of K K)).map (f ≫ g).op) m = _
  rw [show ((f ≫ g).op : Opposite.op Z ⟶ Opposite.op X) = g.op ≫ f.op from rfl,
    CategoryTheory.Functor.map_comp, HomologicalComplex.homologyMap_comp]

/-- If `f ≫ g` is the identity and `g`'s pullback is bijective, so is `f`'s. -/
theorem absPull_bijective_of_compOf (K : Type) [CommRing K] {X Y : TopCat.{0}} (f : X ⟶ Y)
    (g : Y ⟶ X) (hfg : f ≫ g = 𝟙 X) (m : ℕ) (hg : Function.Bijective (absPullOf K g m).hom) :
    Function.Bijective (absPullOf K f m).hom := by
  refine bijective_of_comp_eq_id hg (fun a => ?_)
  have h : absPullOf K g m ≫ absPullOf K f m = 𝟙 ((cochainCx K X).homology m) := by
    rw [← absPull_compOf, hfg, absPull_id_eqOf]
  have h2 := congrArg (fun u => u.hom a) h
  simp only [ModuleCat.comp_apply] at h2
  exact h2

/-! ## 2. The two projections off a contractible factor, over `K` -/

theorem absPull_snd_bijectiveOf (K : Type) [CommRing K] (hB : ContractibleSpace B) (m : ℕ) :
    Function.Bijective (absPullOf K (sndMap B E) m).hom := by
  haveI := hB
  have hb := (pullEquivOfHomotopyEquivOf K (prodSndHomotopyEquiv B E) m).bijective
  rw [show (pullEquivOfHomotopyEquivOf K (prodSndHomotopyEquiv B E) m :
      Hmod K (TopCat.of E) m → Hmod K (TopCat.of (B × E)) m)
      = fun a => pull (cmap (prodSndHomotopyEquiv B E).toFun) m a from rfl,
    prodSndHomotopyEquiv_toFun] at hb
  exact hb

theorem absPull_subSnd_bijectiveOf (K : Type) [CommRing K] (hB : ContractibleSpace B)
    (S : Set E) (m : ℕ) :
    Function.Bijective (absPullOf K (cmap (subSndCMap B S)) m).hom := by
  haveI := hB
  have hb := (pullEquivOfHomotopyEquivOf K (subSndHomotopyEquiv B S) m).bijective
  rw [show (pullEquivOfHomotopyEquivOf K (subSndHomotopyEquiv B S) m :
      Hmod K (TopCat.of ↥S) m → Hmod K (TopCat.of ↥{q : B × E | q.2 ∈ S}) m)
      = fun a => pull (cmap (subSndHomotopyEquiv B S).toFun) m a from rfl,
    subSndHomotopyEquiv_toFun] at hb
  exact hb

/-! ## 3. The slice induces a bijection on relative cohomology -/

theorem relPullback_slice_bijectiveOf (K : Type) [CommRing K] (hB : ContractibleSpace B) (b : B)
    (S : Set E) (n : ℕ) :
    Function.Bijective (relPullback K (sliceMap b E) (slice_mapsTo b S) (n + 1)).hom := by
  refine relPullback_bijective_of_absoluteOf K (sliceMap b E) (slice_mapsTo b S) n
    (fun m => absPull_bijective_of_compOf K (sliceMap b E) (sndMap B E)
      (slice_comp_snd b E) m (absPull_snd_bijectiveOf K hB m))
    (fun m => ?_)
  exact absPull_bijective_of_compOf K (restrictPairMap (sliceMap b E) (slice_mapsTo b S))
    (cmap (subSndCMap B S)) (subSlice_comp_subSnd b S) m (absPull_subSnd_bijectiveOf K hB S m)

/-! ## 4. The bundled isomorphisms -/

/-- **The relative group of a product pair over a contractible base is the relative group of
the fibre pair**, over any commutative ring.  The underlying map is `relPullback` along
`sliceMap`; see `relCohomologyProdIsoGenOf_hom`. -/
def relCohomologyProdIsoGenOf (K : Type) [CommRing K] (hB : ContractibleSpace B) (b : B)
    (n : ℕ) (hn : 2 ≤ n) {E : Type} [TopologicalSpace E] (S : Set E) :
    relCohomology K (TopCat.of (B × E)) {q : B × E | q.2 ∈ S} n
      ≅ relCohomology K (TopCat.of E) S n :=
  haveI : IsIso (relPullback K (sliceMap b E) (slice_mapsTo b S) n) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact (ConcreteCategory.isIso_iff_bijective _).2
      (relPullback_slice_bijectiveOf K hB b S m)
  asIso (relPullback K (sliceMap b E) (slice_mapsTo b S) n)

@[simp] theorem relCohomologyProdIsoGenOf_hom (K : Type) [CommRing K] (hB : ContractibleSpace B)
    (b : B) (n : ℕ) (hn : 2 ≤ n) {E : Type} [TopologicalSpace E] (S : Set E) :
    (relCohomologyProdIsoGenOf K hB b n hn S).hom
      = relPullback K (sliceMap b E) (slice_mapsTo b S) n := rfl

/-- The complex fibre and the complement of the origin, over `K`. -/
def relCohomologyProdIsoOf (K : Type) [CommRing K] (hB : ContractibleSpace B) (b : B)
    (r n : ℕ) (hn : 2 ≤ n) :
    relCohomology K (TopCat.of (B × (Fin r → ℂ))) {q | q.2 ≠ 0} n
      ≅ relCohomology K (TopCat.of (Fin r → ℂ)) (puncturedSet r) n :=
  relCohomologyProdIsoGenOf K hB b n hn (puncturedSet r)

@[simp] theorem relCohomologyProdIsoOf_hom (K : Type) [CommRing K] (hB : ContractibleSpace B)
    (b : B) (r n : ℕ) (hn : 2 ≤ n) :
    (relCohomologyProdIsoOf K hB b r n hn).hom
      = relPullback K (sliceMap b (Fin r → ℂ)) (slice_mapsTo b (puncturedSet r)) n := rfl

end

end RelativeSupport

/-! Audited on every build. -/

#audit_axioms RelativeSupport.relPullback_slice_bijectiveOf

end GroupApproximation.CharClass
