import GroupApproximation.CharClass.CartanDiagonalModule
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.StdSimplex

/-!
# The standard simplex is contractible, so its mod-2 homology vanishes

This is the one piece of geometry the Cartan comparison needs.  The acyclic-models
theorem asks that the target be acyclic *on the models*, and the models are the
topological standard simplices.  Everything else in the comparison is algebra.

The proof is short only because Mathlib already has the hard part.  The
topological `n`-simplex is `ULift` of a convex subset of a real vector space, so
it is contractible; homotopy invariance of singular homology is Mathlib's
`TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor`, valid over any
coefficient object, `ZMod 2` included; and the homology of a point vanishes in
positive degrees because a point is totally disconnected.

## Main results

* `stdSimplexTop_contractibleSpace` — the models are contractible.
* `homZMod2_isZero_of_contractible` — a contractible space has vanishing mod-2
  homology in every positive degree.
* `homZMod2_isZero_stdSimplexTop` — **the input to acyclicity**.
-/

namespace GroupApproximation.CharClass

open CategoryTheory

noncomputable section

/-! ## 1. Mod-2 singular homology as a functor -/

/-- The `k`-th mod-2 singular homology functor. -/
noncomputable abbrev homZMod2 (k : ℕ) : TopCat.{0} ⥤ ModuleCat.{0} (ZMod 2) :=
  (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) k).obj
    (ModuleCat.of (ZMod 2) (ZMod 2))

/-- **Homotopy invariance** at mod-2 coefficients. -/
theorem homZMod2_map_eq_of_homotopy {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom g.hom) (k : ℕ) :
    (homZMod2 k).map f = (homZMod2 k).map g := by
  change HomologicalComplex.homologyMap _ k = HomologicalComplex.homologyMap _ k
  exact (show TopCat.Homotopy f g from H).congr_homologyMap_singularChainComplexFunctor
    (ModuleCat.of (ZMod 2) (ZMod 2)) k

/-- A homotopy equivalence induces an isomorphism on mod-2 homology. -/
def homZMod2IsoOfHomotopyEquiv {Y Z : TopCat.{0}}
    (e : ContinuousMap.HomotopyEquiv Y Z) (k : ℕ) :
    (homZMod2 k).obj Y ≅ (homZMod2 k).obj Z where
  hom := (homZMod2 k).map (TopCat.ofHom e.toFun)
  inv := (homZMod2 k).map (TopCat.ofHom e.invFun)
  hom_inv_id := by
    rw [← Functor.map_comp]
    obtain ⟨H⟩ := e.left_inv
    rw [show TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun
        = TopCat.ofHom (e.invFun.comp e.toFun) from rfl,
      homZMod2_map_eq_of_homotopy (f := TopCat.ofHom (e.invFun.comp e.toFun))
        (g := TopCat.ofHom (ContinuousMap.id Y)) H k,
      show TopCat.ofHom (ContinuousMap.id Y) = 𝟙 Y from rfl, CategoryTheory.Functor.map_id]
  inv_hom_id := by
    rw [← Functor.map_comp]
    obtain ⟨H⟩ := e.right_inv
    rw [show TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun
        = TopCat.ofHom (e.toFun.comp e.invFun) from rfl,
      homZMod2_map_eq_of_homotopy (f := TopCat.ofHom (e.toFun.comp e.invFun))
        (g := TopCat.ofHom (ContinuousMap.id Z)) H k,
      show TopCat.ofHom (ContinuousMap.id Z) = 𝟙 Z from rfl, CategoryTheory.Functor.map_id]

/-- **A contractible space has no mod-2 homology in positive degrees.** -/
theorem homZMod2_isZero_of_contractible (Y : TopCat.{0}) [ContractibleSpace Y]
    (k : ℕ) (hk : k ≠ 0) : Limits.IsZero ((homZMod2 k).obj Y) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit (Y : Type)
  have hUnit : Limits.IsZero ((homZMod2 k).obj (TopCat.of Unit)) :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat.{0} (ZMod 2)) k (ModuleCat.of (ZMod 2) (ZMod 2)) (TopCat.of Unit) hk
  have hIso : (homZMod2 k).obj Y ≅ (homZMod2 k).obj (TopCat.of Unit) :=
    homZMod2IsoOfHomotopyEquiv (Y := Y) (Z := TopCat.of Unit) e k
  exact Limits.IsZero.of_iso hUnit hIso

/-! ## 2. The models are contractible -/

instance stdSimplexTop_contractibleSpace (n : ℕ) :
    ContractibleSpace (stdSimplexTop n) := by
  have hne : (stdSimplex ℝ (Fin (n + 1))).Nonempty :=
    ⟨_, single_mem_stdSimplex ℝ (0 : Fin (n + 1))⟩
  haveI hc : ContractibleSpace ↥(stdSimplex ℝ (Fin (n + 1))) :=
    (convex_stdSimplex ℝ (Fin (n + 1))).contractibleSpace hne
  exact (Homeomorph.ulift (X := ↥(stdSimplex ℝ (Fin (n + 1))))).contractibleSpace

/-- **The models have no mod-2 homology in positive degrees.** -/
theorem homZMod2_isZero_stdSimplexTop (n k : ℕ) (hk : k ≠ 0) :
    Limits.IsZero ((homZMod2 k).obj (stdSimplexTop n)) :=
  homZMod2_isZero_of_contractible (stdSimplexTop n) k hk

end

end GroupApproximation.CharClass
