import Mathlib
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnDegreeOneGenerator
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.ActualRPAlpha
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnMonodromyFunctional
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.MonodromyNontrivial
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnAdditiveCohomology
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnCupProductGenerator
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.H1ClassifierZMod2
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.AlexanderWhitneyChainMap

/-!
# The actual `rpAlpha` equals the model degree-one generator (Prompt 29)

This file proves that the **actual** double-cover / first Stiefel–Whitney class
`actualRPAlpha n` (constructed in `ActualRPAlpha.lean` / `RPnMonodromyFunctional.lean`
from the genuine monodromy of `proj n : Sⁿ → RPⁿ`) coincides with the
**model-identified** degree-one generator `rpDegreeOneGenerator c` of
`RPnDegreeOneGenerator.lean` (the canonical nonzero class of the one-dimensional
`H¹(RPⁿ; F₂)`):

```text
actualRPAlpha n = rpDegreeOneGenerator c          (for 1 ≤ n)
toModel (actualRPAlpha n) = modelAlpha n.
```

## Mathematical route

The two classes live in the same genuine cohomology group `rpCohomology n 1`, which
is one-dimensional over `F₂` (additive computation, conditional on the honest
cellular input `c : RPnCellularCochainStructure n`). A one-dimensional `F₂`-space has
exactly one nonzero element, so it suffices to show that **both classes are
nonzero**:

* `rpDegreeOneGenerator c ≠ 0` is already established (`rpDegreeOneGenerator_ne_zero`);
* `actualRPAlpha n ≠ 0` is the genuine new content. We prove it by exhibiting a
  **fundamental 1-cycle** of `RPⁿ` on which the `w₁` cocycle evaluates to `1`:
  the projection to `RPⁿ` of an explicit path `e ⤳ -e` in `Sⁿ`
  (`rpLoopSimplex`). This is a genuine singular 1-cycle (its two boundary faces
  coincide, because the path's endpoints are antipodal, hence project to the same
  point of `RPⁿ`), and `w1Value` of it is `1` because the lift's endpoints are
  antipodal (`sheetParity_neg`). Pairing through the Kronecker classifier
  (`kroneckerFunctional_apply`) shows `w1Functional n ≠ 0`, hence
  `actualRPAlpha n ≠ 0`.

## Consequence: closing the branch (conditionally on the honest inputs)

With the identification proven, the model bridge's chosen degree-one class equals
the actual monodromy class `rpAlpha n (monodromyFunctional n)`, so the
multiplicative generator-identification structure
`RPnGeneratorIdentification n` is **inhabited** from the standing honest inputs
`c : RPnCellularCochainStructure n` and `cup : RPnCupProductStructure c`
(`rpNGeneratorIdentification_of_cellular_cup`).

All declarations are honest: no fake class, ring, isomorphism, or assumption is
introduced. The genuine cellular-cochain / cup-product inputs `c`, `cup` are the
same standing inputs of Prompts 26–28.
-/

open CategoryTheory AlgebraicTopology Limits
  GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-! ## 1. An explicit fundamental loop of `RPⁿ` -/

/-- The continuous reparametrisation `|Δ¹| → [0,1]` sending a point of the
topological `1`-simplex to its second barycentric coordinate. It maps the
`0`-th vertex to `0` and the `1`-st vertex to `1`. -/
def simplexParam : C(SimplexCategory.toTop.obj (SimplexCategory.mk 1), unitInterval) where
  toFun := fun x => ⟨x.down.val 1, by
    refine ⟨x.down.2.1 1, ?_⟩
    have hle : x.down.val 1 ≤ ∑ i, x.down.val i :=
      Finset.single_le_sum (f := x.down.val) (fun i _ => x.down.2.1 i) (Finset.mem_univ 1)
    rw [x.down.2.2] at hle; exact hle⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_apply (1 : Fin 2)).comp (continuous_subtype_val.comp continuous_uliftDown)

/-- A fixed base point of `Sⁿ`, the first standard unit vector. -/
def rpBasePoint (n : ℕ) : Sphere n :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

/-- The explicit lift `|Δ¹| → Sⁿ` of the fundamental loop: a path in `Sⁿ` from the
base point `e` to its antipode `-e`, reparametrised over the topological
`1`-simplex. Exists for `n ≥ 1` because the sphere is then path-connected
(`joined_antipode`). -/
def rpLiftMap (n : ℕ) (hn : 1 ≤ n) :
    C(SimplexCategory.toTop.obj (SimplexCategory.mk 1), Sphere n) :=
  ((joined_antipode n hn (rpBasePoint n)).somePath).toContinuousMap.comp simplexParam

/-- The fundamental loop `|Δ¹| → RPⁿ`: the projection of `rpLiftMap`. Since the lift
goes from `e` to `-e` and `proj n (-e) = proj n e`, this is a genuine loop. -/
def rpLoopMap (n : ℕ) (hn : 1 ≤ n) :
    C(SimplexCategory.toTop.obj (SimplexCategory.mk 1), RP n) :=
  (proj n).comp (rpLiftMap n hn)

/-- The fundamental loop as a singular `1`-simplex of `RPⁿ`. -/
def rpLoopSimplex (n : ℕ) (hn : 1 ≤ n) : singularSimplices (TopCat.of (RP n)) 1 :=
  ULift.up (TopCat.ofHom (rpLoopMap n hn))

theorem simplexParam_vertex0 : simplexParam (simplexVertex 1 0) = 0 := by
  apply Subtype.ext
  show (simplexVertex 1 0).down.val 1 = (0 : ℝ)
  simp [simplexVertex, stdSimplex.vertex]

theorem simplexParam_vertex1 : simplexParam (simplexVertex 1 1) = 1 := by
  apply Subtype.ext
  show (simplexVertex 1 1).down.val 1 = (1 : ℝ)
  simp [simplexVertex, stdSimplex.vertex]

/-- The fundamental lift starts at the base point. -/
theorem rpLiftMap_vertex0 (n : ℕ) (hn : 1 ≤ n) :
    rpLiftMap n hn (simplexVertex 1 0) = rpBasePoint n := by
  show ((joined_antipode n hn (rpBasePoint n)).somePath) (simplexParam (simplexVertex 1 0)) = _
  rw [simplexParam_vertex0]; simp

/-- The fundamental lift ends at the antipode of the base point. -/
theorem rpLiftMap_vertex1 (n : ℕ) (hn : 1 ≤ n) :
    rpLiftMap n hn (simplexVertex 1 1) = -(rpBasePoint n) := by
  show ((joined_antipode n hn (rpBasePoint n)).somePath) (simplexParam (simplexVertex 1 1)) = _
  rw [simplexParam_vertex1]; simp

/-! ## 2. `w₁` evaluates to `1` on the fundamental loop -/

/-- **The `w₁` value of the fundamental loop is `1`.** Any lift `L` of the loop is
either the fundamental lift or its antipode, so its two endpoint values are
antipodal; by `sheetParity_neg` their sheet parities sum to `1`. -/
theorem w1Value_rpLoopSimplex (n : ℕ) (hn : 1 ≤ n) :
    w1Value n (rpLoopSimplex n hn) = 1 := by
  unfold w1Value
  set L := simplexLift n 1 (rpLoopSimplex n hn) with hL
  have hLspec : (proj n) ∘ L = rpCochainSimplexMap n 1 (rpLoopSimplex n hn) :=
    simplexLift_spec n 1 (rpLoopSimplex n hn)
  have hlift : (proj n) ∘ (rpLiftMap n hn) = rpCochainSimplexMap n 1 (rpLoopSimplex n hn) := rfl
  rcases proj_lift_dichotomy n L (rpLiftMap n hn) hLspec hlift with heq | hanti
  · rw [heq, rpLiftMap_vertex0 n hn, rpLiftMap_vertex1 n hn, sheetParity_neg]
    generalize sheetParity n (rpBasePoint n) = a; revert a; decide
  · rw [hanti (simplexVertex 1 0), hanti (simplexVertex 1 1), rpLiftMap_vertex0 n hn,
      rpLiftMap_vertex1 n hn, sheetParity_neg, neg_neg]
    generalize sheetParity n (rpBasePoint n) = a; revert a; decide

/-! ## 3. The fundamental loop is a singular `1`-cycle -/

/-- Two singular `0`-simplices agree once their underlying continuous maps agree. -/
theorem zeroSimplex_ext (X : TopCat.{0}) (a b : singularSimplices X 0)
    (h : (a.down.hom : C(_, X)) = b.down.hom) : a = b := by
  apply ULift.ext; apply TopCat.hom_ext; exact h

/-- **The singular chain boundary on a generator.** The boundary of the basis chain
of a `1`-simplex `σ` is the alternating sum of the basis chains of its two
boundary faces. -/
theorem chain_d_generator (X : TopCat.{0}) (σ : singularSimplices X 1) :
    ((chainCxZMod2 X).d 1 0).hom
        ((Sigma.ι (fun (_ : singularSimplices X 1) => ModuleCat.of (ZMod 2) (ZMod 2)) σ).hom
          (1 : ZMod 2))
      = ∑ i : Fin 2, ((-1 : ℤ) ^ (i : ℕ)) •
          ((Sigma.ι (fun (_ : singularSimplices X 0) => ModuleCat.of (ZMod 2) (ZMod 2))
            (faceSimplex X 0 i σ)).hom (1 : ZMod 2)) := by
  rw [show (chainCxZMod2 X).d 1 0
        = (AlternatingFaceMapComplex.obj (singularChainSimplicialModule (ZMod 2) X)).d 1 0 from rfl,
    AlternatingFaceMapComplex.obj_d_eq, ModuleCat.hom_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [ModuleCat.hom_zsmul, LinearMap.smul_apply]
  erw [singularChainSimplicialModule_δ_generator (ZMod 2) X 0 i σ]

/-- **The two boundary faces of the fundamental loop coincide.** Both are the
same `0`-simplex at `proj n e = proj n (-e)`. -/
theorem rpLoop_faces_eq (n : ℕ) (hn : 1 ≤ n) :
    faceSimplex (TopCat.of (RP n)) 0 0 (rpLoopSimplex n hn)
      = faceSimplex (TopCat.of (RP n)) 0 1 (rpLoopSimplex n hn) := by
  have heq : (rpCochainSimplexMap n 1 (rpLoopSimplex n hn)) (simplexVertex 1 1)
           = (rpCochainSimplexMap n 1 (rpLoopSimplex n hn)) (simplexVertex 1 0) := by
    show proj n (rpLiftMap n hn (simplexVertex 1 1)) = proj n (rpLiftMap n hn (simplexVertex 1 0))
    rw [rpLiftMap_vertex0 n hn, rpLiftMap_vertex1 n hn, proj_neg]
  apply zeroSimplex_ext
  have e0 : (faceSimplex (TopCat.of (RP n)) 0 0 (rpLoopSimplex n hn)).down.hom
      = rpCochainSimplexMap n 0 (faceSimplex (TopCat.of (RP n)) 0 0 (rpLoopSimplex n hn)) := rfl
  have e1 : (faceSimplex (TopCat.of (RP n)) 0 1 (rpLoopSimplex n hn)).down.hom
      = rpCochainSimplexMap n 0 (faceSimplex (TopCat.of (RP n)) 0 1 (rpLoopSimplex n hn)) := rfl
  rw [e0, e1, rpCochainSimplexMap_face0, rpCochainSimplexMap_face0]
  ext t
  have ht : t = simplexVertex 0 0 := Subsingleton.elim _ _
  subst ht
  show (rpCochainSimplexMap n 1 (rpLoopSimplex n hn))
        ((SimplexCategory.toTop.map (SimplexCategory.δ 0)).hom (simplexVertex 0 0))
     = (rpCochainSimplexMap n 1 (rpLoopSimplex n hn))
        ((SimplexCategory.toTop.map (SimplexCategory.δ 1)).hom (simplexVertex 0 0))
  rw [toTop_delta0_vertex, toTop_delta0_vertex,
      show Fin.succAbove (0 : Fin 2) (0 : Fin 1) = 1 from by decide,
      show Fin.succAbove (1 : Fin 2) (0 : Fin 1) = 0 from by decide]
  exact heq

/-- **The fundamental loop is a singular `1`-cycle.** -/
theorem rpLoop_is_cycle (n : ℕ) (hn : 1 ≤ n) :
    ((chainCxZMod2 (TopCat.of (RP n))).d 1 0).hom
        ((Sigma.ι (fun (_ : singularSimplices (TopCat.of (RP n)) 1) =>
          ModuleCat.of (ZMod 2) (ZMod 2)) (rpLoopSimplex n hn)).hom (1 : ZMod 2)) = 0 := by
  rw [chain_d_generator, Fin.sum_univ_two, rpLoop_faces_eq n hn]
  generalize (Sigma.ι (fun (_ : singularSimplices (TopCat.of (RP n)) 0) =>
    ModuleCat.of (ZMod 2) (ZMod 2))
      (faceSimplex (TopCat.of (RP n)) 0 1 (rpLoopSimplex n hn))).hom (1 : ZMod 2) = g
  simp

/-! ## 4. Nonvanishing of `actualRPAlpha` -/

/-- **The `w₁` monodromy functional is nonzero** for `n ≥ 1`: it pairs to `1` with
the homology class of the fundamental loop. -/
theorem w1Functional_ne_zero (n : ℕ) (hn : 1 ≤ n) : w1Functional n ≠ 0 := by
  set X := TopCat.of (RP n)
  set z := (Sigma.ι (fun (_ : singularSimplices X 1) => ModuleCat.of (ZMod 2) (ZMod 2))
      (rpLoopSimplex n hn)).hom (1 : ZMod 2) with hzdef
  have hz : ((chainCxZMod2 X).d 1 0).hom z = 0 := rpLoop_is_cycle n hn
  set c := (chainCxZMod2 X).cyclesMk z 0
    (by rw [ComplexShape.next_eq' _ (show (ComplexShape.down ℕ).Rel 1 0 by simp)]) hz with hcdef
  have hic : ((chainCxZMod2 X).iCycles 1).hom c = z := by
    have := HomologicalComplex.i_cyclesMk (chainCxZMod2 X) z 0
      (by rw [ComplexShape.next_eq' _ (show (ComplexShape.down ℕ).Rel 1 0 by simp)]) hz
    simpa using this
  have hval : (w1Functional n) (((chainCxZMod2 X).homologyπ 1).hom c) = 1 := by
    show ((kroneckerMap X 1).hom (rpW1Class n)) (((chainCxZMod2 X).homologyπ 1).hom c) = 1
    rw [show rpW1Class n = cocycleClass X 1 (w1Cochain n) (w1Cochain_cocycle n) from rfl,
      kroneckerMap_cocycleClass]
    rw [kroneckerFunctional_apply X 1 (w1Cochain n) (w1Cochain_cocycle n) c, hic]
    show (w1Cochain n).hom z = 1
    rw [hzdef]
    show cochainEval 1 (w1Cochain n) (rpLoopSimplex n hn) = 1
    rw [w1Cochain_eval, w1Value_rpLoopSimplex n hn]
  intro h0
  rw [h0] at hval
  simp at hval

/-- **The actual canonical class `actualRPAlpha n` is nonzero** for `n ≥ 1`. -/
theorem actualRPAlpha_ne_zero (n : ℕ) (hn : 1 ≤ n) : actualRPAlpha n ≠ 0 := by
  intro h
  apply w1Functional_ne_zero n hn
  rw [← actualRPAlpha_kroneckerMap n, h, map_zero]

/-! ## 5. The identification -/

/-- In an `F₂`-module isomorphic to `F₂`, any two nonzero elements are equal (`F₂`
has a unique nonzero element). -/
theorem eq_of_ne_zero_of_isoF2 {M : ModuleCat.{0} (ZMod 2)}
    (e : M ≅ ModuleCat.of (ZMod 2) (ZMod 2)) (a b : M) (ha : a ≠ 0) (hb : b ≠ 0) : a = b := by
  have hea : e.toLinearEquiv a ≠ 0 := by simpa using (e.toLinearEquiv.map_ne_zero_iff).2 ha
  have heb : e.toLinearEquiv b ≠ 0 := by simpa using (e.toLinearEquiv.map_ne_zero_iff).2 hb
  have h1 : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  apply e.toLinearEquiv.injective
  rw [h1 _ hea, h1 _ heb]

/-- **Main result: the actual `rpAlpha` is the model degree-one generator.** For
`n ≥ 1` the actual double-cover/`w₁` class coincides with the model-identified
degree-one generator (both are the unique nonzero class of the one-dimensional
`H¹(RPⁿ; F₂)`). Conditional on the honest cellular-cochain input `c`. -/
theorem actualRPAlpha_eq_rpDegreeOneGenerator (n : ℕ) (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n) :
    actualRPAlpha n = rpDegreeOneGenerator c :=
  eq_of_ne_zero_of_isoF2 (rpH1ZMod2_iso c hn) _ _
    (actualRPAlpha_ne_zero n hn) (rpDegreeOneGenerator_ne_zero c hn)

/-- **Model image of the actual `rpAlpha`.** The additive comparison carries the
actual `α = w₁` to the model degree-one generator `modelAlpha n`. -/
theorem toModel_actualRPAlpha_eq_modelAlpha (n : ℕ) (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n) :
    rpCohomologyToModelToFun c 1 (actualRPAlpha n) = modelAlpha n := by
  rw [actualRPAlpha_eq_rpDegreeOneGenerator n hn c, toModel_rpDegreeOneGenerator c]

/-- The ring bridge's chosen degree-one class is exactly the actual monodromy class
`rpAlpha n (monodromyFunctional n) = actualRPAlpha n`. -/
theorem rpCohomologyToModelHom_alpha_eq_actualRPAlpha (n : ℕ) (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n) (cup : RPnCupProductStructure c) :
    (rpCohomologyToModelHom c cup).alpha = actualRPAlpha n := by
  rw [rpCohomologyToModelHom_alpha_eq c cup, ← actualRPAlpha_eq_rpDegreeOneGenerator n hn c]

/-! ## 6. Closing the `RPnGeneratorIdentification` branch

With the identification proven, the multiplicative generator-identification
structure is inhabited from the standing honest inputs `c` and `cup`. -/

/-- **Branch closure (conditional on the honest inputs).** From the cellular-cochain
input `c` and the cup-product input `cup`, the multiplicative generator
identification `RPnGeneratorIdentification n` is constructed, with its model
bridge's degree-one class taken to be the actual monodromy class
`actualRPAlpha n`. -/
def rpNGeneratorIdentification_of_cellular_cup (n : ℕ) (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n) (cup : RPnCupProductStructure c) :
    RPnGeneratorIdentification n :=
  rpNGeneratorIdentification_of_inputs n (monodromyFunctional n) (rpCohomologyToModelHom c cup)
    (by
      show (rpCohomologyToModelHom c cup).alpha = rpAlpha n (monodromyFunctional n)
      rw [rpCohomologyToModelHom_alpha_eq_actualRPAlpha n hn c cup, actualRPAlpha_eq_rpAlpha])

/-- **The branch target is inhabited** from the honest cellular and cup-product
inputs. -/
theorem nonempty_rpNGeneratorIdentification_of_cellular_cup (n : ℕ) (hn : 1 ≤ n)
    (c : RPnCellularCochainStructure n) (cup : RPnCupProductStructure c) :
    Nonempty (RPnGeneratorIdentification n) :=
  ⟨rpNGeneratorIdentification_of_cellular_cup n hn c cup⟩

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
