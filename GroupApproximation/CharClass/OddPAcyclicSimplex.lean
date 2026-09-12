import GroupApproximation.CharClass.OddPSingular
import GroupApproximation.CharClass.CartanSimplexContractible
import GroupApproximation.CharClass.AcyclicModelsHomology
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Over a standard simplex, positive-degree cycles of the signed singular complex are boundaries

Lane `lix-cupone`, block `OddPAcyclic*` (lix-steenrod's plan §3.4, input (a)).

`CartanSimplexExact.lean` proves this at `ZMod 2` for the `Finsupp`-carrier complex, and its chain-map
step goes through the vendored `singular_d_ι`, whose *statement* is the unsigned face sum.  That is
characteristic two in the shape of a statement (sp-steenrod §1.2a), so it is not ported and not used.

This file re-derives the signed statement with no face sum at all.  Both complexes are the
alternating face map complex of a simplicial module:

* `singFreeR K` (`OddPSingular`) applies `ModuleCat.free K` levelwise, carrier `σ-simplices →₀ K`;
* Mathlib's `singularChainComplexFunctor` applies `sigmaConst.obj (ModuleCat.of K K)` levelwise,
  carrier the coproduct of one copy of `K` per simplex.

The two levelwise functors are isomorphic because they are left adjoint to isomorphic functors —
`free K ⊣ forget` and `sigmaConst.obj K ⊣ Hom(K, -)`, with `Hom(K, M) ≅ M` — so
`Adjunction.leftAdjointUniq` gives the isomorphism with no computation, and
`alternatingFaceMapComplex.mapIso` turns it into an isomorphism of chain complexes.  An isomorphism
of simplicial objects carries the alternating signs on both sides by construction, which is exactly
what the mod-2 bridge could not do.  Homology then transports, the homology of a contractible space
vanishes in positive degrees (Mathlib's homotopy invariance, at coefficients `K`), and
`exists_preimage_of_isZero_homology` reads that off on elements.

No field is needed here; the export is stated over `[CommRing K]`.

## Main declarations

* `OddPAcyclic.coyonedaUnitIsoForget`, `OddPAcyclic.freeIsoSigmaConst` — the levelwise isomorphism.
* `OddPAcyclic.singFreeRIsoSingular` — the chain isomorphism with Mathlib's singular complex.
* `OddPAcyclic.singFreeR_isZero_homology_stdSimplexTop` — vanishing homology on the models.
* `OddPAcyclic.singFreeR_ker_le_range_stdSimplexTop` — **the acyclicity input**, in the
  `AcyclicModelsSplitting` form.
-/

namespace GroupApproximation.CharClass

open CategoryTheory AlgebraicTopology Limits

noncomputable section

namespace OddPAcyclic

variable (K : Type) [CommRing K]

/-! ## 1. The levelwise isomorphism `free K ≅ sigmaConst.obj K` -/

/-- `Hom(K, M) ≃ M`: evaluate at `1`. -/
def unitHomEquiv (M : ModuleCat.{0} K) : (ModuleCat.of K K ⟶ M) ≃ M where
  toFun f := f.hom (1 : K)
  invFun m := ModuleCat.ofHom (LinearMap.toSpanSingleton K M m)
  left_inv f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    simp only [ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply_one]
  right_inv m := by
    simp only [ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply_one]

/-- `Hom(K, M) ≅ M`, naturally in the module `M`. -/
def coyonedaUnitIsoForget :
    coyoneda.obj (Opposite.op (ModuleCat.of K K)) ≅ forget (ModuleCat.{0} K) :=
  NatIso.ofComponents (fun M => (unitHomEquiv K M).toIso)
    (fun {M N} g => by
      ext f
      rfl)

/-- **The two levelwise functors are isomorphic**, as left adjoints of isomorphic functors. -/
def freeIsoSigmaConst :
    ModuleCat.free K ≅ sigmaConst.obj (ModuleCat.of K K) :=
  (ModuleCat.adj K).leftAdjointUniq
    ((sigmaConstAdj (ModuleCat.of K K)).ofNatIsoRight (coyonedaUnitIsoForget K))

/-- **The signed `Finsupp` singular complex is Mathlib's singular complex**, up to an isomorphism
of chain complexes induced by an isomorphism of simplicial modules. -/
def singFreeRIsoSingular (X : TopCat.{0}) :
    (alternatingFaceMapComplex (ModuleCat.{0} K)).obj (TopCat.toSSet.obj X ⋙ ModuleCat.free K)
      ≅ (alternatingFaceMapComplex (ModuleCat.{0} K)).obj
          (TopCat.toSSet.obj X ⋙ sigmaConst.obj (ModuleCat.of K K)) :=
  (alternatingFaceMapComplex (ModuleCat.{0} K)).mapIso
    (Functor.isoWhiskerLeft (TopCat.toSSet.obj X) (freeIsoSigmaConst K))

/-! ## 2. Vanishing homology on the models, over `K` -/

/-- The `k`-th singular homology functor with coefficients in `K`. -/
abbrev homOf (k : ℕ) : TopCat.{0} ⥤ ModuleCat.{0} K :=
  (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} K) k).obj (ModuleCat.of K K)

theorem homOf_map_eq_of_homotopy {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom g.hom) (k : ℕ) :
    (homOf K k).map f = (homOf K k).map g := by
  change HomologicalComplex.homologyMap _ k = HomologicalComplex.homologyMap _ k
  exact (show TopCat.Homotopy f g from H).congr_homologyMap_singularChainComplexFunctor
    (ModuleCat.of K K) k

/-- A homotopy equivalence induces an isomorphism on homology with coefficients in `K`. -/
def homOfIsoOfHomotopyEquiv {Y Z : TopCat.{0}} (e : ContinuousMap.HomotopyEquiv Y Z) (k : ℕ) :
    (homOf K k).obj Y ≅ (homOf K k).obj Z where
  hom := (homOf K k).map (TopCat.ofHom e.toFun)
  inv := (homOf K k).map (TopCat.ofHom e.invFun)
  hom_inv_id := by
    rw [← Functor.map_comp]
    obtain ⟨H⟩ := e.left_inv
    rw [show TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun
        = TopCat.ofHom (e.invFun.comp e.toFun) from rfl,
      homOf_map_eq_of_homotopy K (f := TopCat.ofHom (e.invFun.comp e.toFun))
        (g := TopCat.ofHom (ContinuousMap.id Y)) H k,
      show TopCat.ofHom (ContinuousMap.id Y) = 𝟙 Y from rfl, CategoryTheory.Functor.map_id]
  inv_hom_id := by
    rw [← Functor.map_comp]
    obtain ⟨H⟩ := e.right_inv
    rw [show TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun
        = TopCat.ofHom (e.toFun.comp e.invFun) from rfl,
      homOf_map_eq_of_homotopy K (f := TopCat.ofHom (e.toFun.comp e.invFun))
        (g := TopCat.ofHom (ContinuousMap.id Z)) H k,
      show TopCat.ofHom (ContinuousMap.id Z) = 𝟙 Z from rfl, CategoryTheory.Functor.map_id]

/-- **A contractible space has no homology with coefficients in `K` in positive degrees.** -/
theorem homOf_isZero_of_contractible (Y : TopCat.{0}) [ContractibleSpace Y] (k : ℕ)
    (hk : k ≠ 0) : IsZero ((homOf K k).obj Y) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit (Y : Type)
  have hUnit : IsZero ((homOf K k).obj (TopCat.of Unit)) :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat.{0} K) k (ModuleCat.of K K) (TopCat.of Unit) hk
  exact IsZero.of_iso hUnit (homOfIsoOfHomotopyEquiv K (Y := Y) (Z := TopCat.of Unit) e k)

/-- **The signed `Finsupp` complex of a standard simplex has no positive-degree homology.** -/
theorem singFreeR_isZero_homology_stdSimplexTop (n k : ℕ) :
    IsZero (((singFreeR K).obj (stdSimplexTop n)).homology (k + 1)) := by
  have hM : IsZero (((alternatingFaceMapComplex (ModuleCat.{0} K)).obj
      (TopCat.toSSet.obj (stdSimplexTop n) ⋙ sigmaConst.obj (ModuleCat.of K K))).homology
        (k + 1)) :=
    homOf_isZero_of_contractible K (stdSimplexTop n) (k + 1) (Nat.succ_ne_zero k)
  exact IsZero.of_iso hM
    (HomologicalComplex.homologyMapIso (singFreeRIsoSingular K (stdSimplexTop n)) (k + 1))

/-- **The acyclicity input on the models**, in the form `AcyclicModelsSplitting` consumes: over a
standard simplex every positive-degree cycle of the signed singular complex is a boundary. -/
theorem singFreeR_ker_le_range_stdSimplexTop (n : ℕ) :
    ∀ k : ℕ, LinearMap.ker (((singFreeR K).obj (stdSimplexTop n)).d (k + 1) k).hom
      ≤ LinearMap.range (((singFreeR K).obj (stdSimplexTop n)).d (k + 2) (k + 1)).hom := by
  intro k y hy
  obtain ⟨z, hz⟩ := exists_preimage_of_isZero_homology ((singFreeR K).obj (stdSimplexTop n)) k
    (singFreeR_isZero_homology_stdSimplexTop K n k) y hy
  exact ⟨z, hz⟩

end OddPAcyclic

/-- Over every commutative ring, a positive-degree cycle of the signed singular chain complex of a
standard simplex is a boundary. -/
def PrintedSignedSimplexExact : Prop :=
  ∀ (K : Type) [CommRing K] (n k : ℕ),
    LinearMap.ker (((singFreeR K).obj (stdSimplexTop n)).d (k + 1) k).hom
      ≤ LinearMap.range (((singFreeR K).obj (stdSimplexTop n)).d (k + 2) (k + 1)).hom

theorem printedSignedSimplexExact : PrintedSignedSimplexExact := by
  intro K _ n k
  exact OddPAcyclic.singFreeR_ker_le_range_stdSimplexTop K n k

#audit_closed_axioms printedSignedSimplexExact

end

end GroupApproximation.CharClass
