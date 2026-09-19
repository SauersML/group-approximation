import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnW1Cochain
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.ConstructRPAlpha
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.KroneckerNaturality
import Mathlib

/-!
# The monodromy functional of `RPⁿ` from the `w₁` cocycle

This file completes Prompt 18: it constructs the genuine `MonodromyFunctional n`
of `ConstructRPAlpha.lean` from the actual double-cover monodromy, namely the
Kronecker functional of the first Stiefel–Whitney class `rpW1Class n`
(`RPnW1Cochain.lean`).

The two ingredients are:

* **odd-map invariance** of `rpW1Class`: a descended odd map `fbar = inducedOnRP
  f hf` fixes `w₁` in cohomology (`rpW1Class_inducedOnRP_invariant`). At the
  cochain level `fbar^*(w1Cochain)` differs from `w1Cochain` by the coboundary of
  the explicit `0`-cochain `w1DefectCochain` recording how `f` permutes the
  section sheets; the difference is exactly a coboundary, so the classes agree.
* **the Kronecker dual**: `monodromyFunctional n` is the functional
  `⟨rpW1Class n, –⟩` on `H₁(RPⁿ; F₂)`, whose invariance under the homology
  pushforward follows from the cohomological invariance via naturality of the
  Kronecker pairing.

## Main declarations

* `oddDefect`, `sheetParity_section`, `sheetParity_oddMap`;
* `w1Value_push`;
* `w1DefectCochain`, `w1DefectCochain_eval`, `w1DefectCochain_coboundary_eval`;
* `cochainPullback_w1Cochain`;
* `cocycleClass_add`;
* `rpW1Class_inducedOnRP_invariant`;
* `monodromyFunctional n : MonodromyFunctional n` — the target of Prompt 18;
* `rpAlphaW1 n` — the canonical degree-one class `rpAlpha n (monodromyFunctional n)`.
-/

open CategoryTheory AlgebraicTopology Limits
  GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-! ## 1. The sheet defect of an odd map -/

/-- The **sheet defect** of an odd map `f` over a point `q ∈ RPⁿ`: the sheet
parity of `f` applied to the chosen section value over `q`. -/
def oddDefect (n : ℕ) (f : C(Sphere n, Sphere n)) (q : RP n) : ZMod 2 :=
  sheetParity n (f (rpSection n q))

/-- The chosen section value has sheet parity `0`. -/
theorem sheetParity_section (n : ℕ) (q : RP n) : sheetParity n (rpSection n q) = 0 := by
  unfold sheetParity; rw [if_pos]; rw [proj_rpSection]

/-- **Sheet parity under an odd map.** `sheetParity (f p) = sheetParity p +
oddDefect (proj p)`: the odd map shifts the sheet parity by an amount depending
only on the base point. -/
theorem sheetParity_oddMap (n : ℕ) (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) (p : Sphere n) :
    sheetParity n (f p) = sheetParity n p + oddDefect n f (proj n p) := by
  set s := rpSection n (proj n p) with hs
  have hsfib : proj n s = proj n p := by rw [hs, proj_rpSection]
  have hcases : p = s ∨ p = -s := (proj_eq_iff (n := n) (x := s) (y := p)).mp hsfib.symm
  unfold oddDefect; rw [← hs]
  rcases hcases with hp | hp
  · have h0 : sheetParity n p = 0 := by rw [hp, hs, sheetParity_section]
    rw [h0, hp]; ring
  · have h1 : sheetParity n p = 1 := by
      rw [hp, sheetParity_neg, hs, sheetParity_section]; decide
    rw [h1, hp, hf.apply_neg, sheetParity_neg]; ring

/-! ## 2. The `w₁` value of a pushforward simplex -/

/-- **The `w₁` value of a pushforward simplex.** For a descended odd map `fbar =
inducedOnRP f hf` and a singular `1`-simplex `τ`, the value of `w₁` on the
pushforward `fbar ∘ τ` differs from that on `τ` by the sum of the sheet defects at
the two endpoints. -/
theorem w1Value_push (n : ℕ) (f : C(Sphere n, Sphere n)) (hf : IsOddMap f)
    (τ : singularSimplices (TopCat.of (RP n)) 1) :
    w1Value n ((TopCat.toSSet.map (TopCat.ofHom (inducedOnRP f hf))).app
        (Opposite.op (SimplexCategory.mk 1)) τ)
      = w1Value n τ
        + oddDefect n f (rpCochainSimplexMap n 1 τ (simplexVertex 1 0))
        + oddDefect n f (rpCochainSimplexMap n 1 τ (simplexVertex 1 1)) := by
  set fbar := inducedOnRP f hf with hfbar
  set push := (TopCat.toSSet.map (TopCat.ofHom fbar)).app (Opposite.op (SimplexCategory.mk 1)) τ
    with hpush
  set L := simplexLift n 1 τ with hL
  have hLspec : (proj n) ∘ L = rpCochainSimplexMap n 1 τ := simplexLift_spec n 1 τ
  let Lf : C(SimplexCategory.toTop.obj (SimplexCategory.mk 1), Sphere n) := f.comp L
  have hpushmap : rpCochainSimplexMap n 1 push = fbar.comp (rpCochainSimplexMap n 1 τ) := by
    unfold rpCochainSimplexMap; ext t; rfl
  have hLf : (proj n) ∘ Lf = rpCochainSimplexMap n 1 push := by
    rw [hpushmap]; ext t
    show proj n (f (L t)) = fbar (rpCochainSimplexMap n 1 τ t)
    rw [hfbar, show rpCochainSimplexMap n 1 τ t = proj n (L t) from (congrFun hLspec t).symm,
      inducedOnRP_proj]
  set Lpush := simplexLift n 1 push with hLpush
  have hLpushspec : (proj n) ∘ Lpush = rpCochainSimplexMap n 1 push := simplexLift_spec n 1 push
  have hdich := proj_lift_dichotomy n Lpush Lf hLpushspec hLf
  have key : ∀ j : Fin 2, sheetParity n (Lf (simplexVertex 1 j))
      = sheetParity n (L (simplexVertex 1 j))
        + oddDefect n f (rpCochainSimplexMap n 1 τ (simplexVertex 1 j)) := by
    intro j
    show sheetParity n (f (L (simplexVertex 1 j))) = _
    rw [sheetParity_oddMap n f hf,
      show proj n (L (simplexVertex 1 j)) = rpCochainSimplexMap n 1 τ (simplexVertex 1 j)
        from congrFun hLspec _]
  have hval : w1Value n push
      = sheetParity n (Lpush (simplexVertex 1 0)) + sheetParity n (Lpush (simplexVertex 1 1)) := rfl
  have hwτ : w1Value n τ
      = sheetParity n (L (simplexVertex 1 0)) + sheetParity n (L (simplexVertex 1 1)) := rfl
  rw [hval, hwτ]
  rcases hdich with heq | hanti
  · rw [heq, key 0, key 1]; ring
  · rw [hanti (simplexVertex 1 0), hanti (simplexVertex 1 1), sheetParity_neg, sheetParity_neg,
      key 0, key 1]
    generalize sheetParity n (L (simplexVertex 1 0)) = a
    generalize sheetParity n (L (simplexVertex 1 1)) = b
    generalize oddDefect n f (rpCochainSimplexMap n 1 τ (simplexVertex 1 0)) = c
    generalize oddDefect n f (rpCochainSimplexMap n 1 τ (simplexVertex 1 1)) = d
    revert a b c d; decide

/-! ## 3. The defect `0`-cochain and its coboundary -/

/-- The **sheet-defect `0`-cochain** of an odd map: the `0`-cochain whose value on
a `0`-simplex is the sheet defect of `f` at its image point. -/
def w1DefectCochain (n : ℕ) (f : C(Sphere n, Sphere n)) :
    singularCochainGroup (ZMod 2) (TopCat.of (RP n)) 0 :=
  Sigma.desc (fun (τ : singularSimplices (TopCat.of (RP n)) 0) =>
    ModuleCat.ofHom ((oddDefect n f (rpCochainSimplexMap n 0 τ (simplexVertex 0 0)))
      • (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2)))

/-- Evaluation of the defect `0`-cochain. -/
theorem w1DefectCochain_eval (n : ℕ) (f : C(Sphere n, Sphere n))
    (τ : singularSimplices (TopCat.of (RP n)) 0) :
    cochainEval 0 (w1DefectCochain n f) τ
      = oddDefect n f (rpCochainSimplexMap n 0 τ (simplexVertex 0 0)) := by
  change ModuleCat.Hom.hom (Sigma.ι
      (fun (_ : singularSimplices (TopCat.of (RP n)) 0) =>
        ModuleCat.of (ZMod 2) (ZMod 2)) τ ≫
    Sigma.desc (fun (ρ : singularSimplices (TopCat.of (RP n)) 0) =>
      ModuleCat.ofHom
        (oddDefect n f (rpCochainSimplexMap n 0 ρ (simplexVertex 0 0)) •
          (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2)))) (1 : ZMod 2) = _
  rw [Sigma.ι_desc]
  simp

/-- The degree-`0` boundary face of a singular `1`-simplex, as a continuous map,
is the simplex precomposed with the geometric face inclusion `|Δ⁰| → |Δ¹|`. -/
theorem rpCochainSimplexMap_face0 (n : ℕ) (i : Fin 2) (σ : singularSimplices (TopCat.of (RP n)) 1) :
    rpCochainSimplexMap n 0 (faceSimplex (TopCat.of (RP n)) 0 i σ)
      = (rpCochainSimplexMap n 1 σ).comp (SimplexCategory.toTop.map (SimplexCategory.δ i)).hom := by
  unfold rpCochainSimplexMap faceSimplex; ext t; rfl

/-- The geometric face inclusion `δ i : |Δ⁰| → |Δ¹|` sends the vertex to the
`(δ i 0)`-th vertex. -/
theorem toTop_delta0_vertex (i : Fin 2) :
    (SimplexCategory.toTop.map (SimplexCategory.δ i)).hom (simplexVertex 0 0)
      = simplexVertex 1 (Fin.succAbove i 0) := by
  rw [SimplexCategory.toTop_map]
  show ULift.up (stdSimplex.map _ (stdSimplex.vertex 0))
    = ULift.up (stdSimplex.vertex (Fin.succAbove i 0))
  rw [stdSimplex.map_vertex]; congr 1

/-- **Coboundary of the defect cochain on a `1`-simplex**: it is exactly the sum of
the sheet defects at the two endpoints. -/
theorem w1DefectCochain_coboundary_eval (n : ℕ) (f : C(Sphere n, Sphere n))
    (σ : singularSimplices (TopCat.of (RP n)) 1) :
    cochainEval 1 (cochainCoboundary (ZMod 2) (TopCat.of (RP n)) 0 (w1DefectCochain n f)) σ
      = oddDefect n f (rpCochainSimplexMap n 1 σ (simplexVertex 1 0))
        + oddDefect n f (rpCochainSimplexMap n 1 σ (simplexVertex 1 1)) := by
  rw [cochainCoboundary_eval, Fin.sum_univ_two]
  have hface : ∀ i : Fin 2,
      cochainEval 0 (w1DefectCochain n f) (faceSimplex (TopCat.of (RP n)) 0 i σ)
        = oddDefect n f (rpCochainSimplexMap n 1 σ (simplexVertex 1 (Fin.succAbove i 0))) := by
    intro i
    rw [w1DefectCochain_eval, rpCochainSimplexMap_face0]
    show oddDefect n f ((rpCochainSimplexMap n 1 σ) ((SimplexCategory.toTop.map (SimplexCategory.δ i)).hom
      (simplexVertex 0 0))) = _
    rw [toTop_delta0_vertex]
  rw [hface 0, hface 1]
  have s0 : Fin.succAbove (0 : Fin 2) (0 : Fin 1) = 1 := by decide
  have s1 : Fin.succAbove (1 : Fin 2) (0 : Fin 1) = 0 := by decide
  rw [s0, s1]
  generalize oddDefect n f (rpCochainSimplexMap n 1 σ (simplexVertex 1 0)) = a
  generalize oddDefect n f (rpCochainSimplexMap n 1 σ (simplexVertex 1 1)) = b
  revert a b; decide

/-! ## 4. The cochain identity and class invariance -/

/-- **Cochain identity.** The pullback of the `w₁` cochain along a descended odd
map differs from `w₁` by the coboundary of the defect cochain. -/
theorem cochainPullback_w1Cochain (n : ℕ) (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    cochainPullback (TopCat.ofHom (inducedOnRP f hf)) 1 (w1Cochain n)
      = w1Cochain n + cochainCoboundary (ZMod 2) (TopCat.of (RP n)) 0 (w1DefectCochain n f) := by
  apply cochain_ext
  intro σ
  rw [cochainPullback_eval, w1Cochain_eval, w1Value_push n f hf]
  rw [cochainEval_add, w1Cochain_eval, w1DefectCochain_coboundary_eval]
  ring

/-
Additivity of the cohomology class of cocycles.
-/
theorem cocycleClass_add (X : TopCat.{0}) (n : ℕ)
    (φ ψ : singularCochainGroup (ZMod 2) X n)
    (hφ : cochainCoboundary (ZMod 2) X n φ = 0) (hψ : cochainCoboundary (ZMod 2) X n ψ = 0)
    (hφψ : cochainCoboundary (ZMod 2) X n (φ + ψ) = 0) :
    cocycleClass X n (φ + ψ) hφψ = cocycleClass X n φ hφ + cocycleClass X n ψ hψ := by
  unfold cocycleClass
  rw [← map_add]
  apply congrArg ((cochainCxZMod2 X).homologyπ n).hom
  apply (ModuleCat.mono_iff_injective ((cochainCxZMod2 X).iCycles n)).1 inferInstance
  rw [iCycles_cyclesMk, map_add, iCycles_cyclesMk, iCycles_cyclesMk]

/-- **Odd-map invariance of `w₁`.** A descended odd map `fbar = inducedOnRP f hf`
fixes the first Stiefel–Whitney class in `H¹(RPⁿ; F₂)`. -/
theorem rpW1Class_inducedOnRP_invariant (n : ℕ) (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    (cohPullback (TopCat.ofHom (inducedOnRP f hf)) 1).hom (rpW1Class n) = rpW1Class n := by
  have hid := cochainPullback_w1Cochain n f hf
  have h2 : cochainCoboundary (ZMod 2) (TopCat.of (RP n)) 1
      (w1Cochain n + cochainCoboundary (ZMod 2) (TopCat.of (RP n)) 0 (w1DefectCochain n f)) = 0 := by
    rw [← hid]; exact cochainPullback_cocycle _ 1 (w1Cochain n) (w1Cochain_cocycle n)
  rw [rpW1Class, cohPullback_cocycleClass]
  rw [cocycleClass_congr (TopCat.of (RP n)) 1 hid
    (cochainPullback_cocycle _ 1 (w1Cochain n) (w1Cochain_cocycle n)) h2]
  rw [cocycleClass_add (TopCat.of (RP n)) 1 (w1Cochain n)
    (cochainCoboundary (ZMod 2) (TopCat.of (RP n)) 0 (w1DefectCochain n f))
    (w1Cochain_cocycle n)
    (cochainCoboundary_cochainCoboundary (TopCat.of (RP n)) 0 (w1DefectCochain n f))]
  rw [cocycleClass_coboundary_zero, add_zero]

/-! ## 5. The monodromy functional -/

/-- The Kronecker dual functional `g = ⟨rpW1Class, –⟩ : H₁(RPⁿ; F₂) → F₂`. -/
def w1Functional (n : ℕ) : homologyZMod2 (TopCat.of (RP n)) 1 →ₗ[ZMod 2] ZMod 2 :=
  (kroneckerMap (TopCat.of (RP n)) 1).hom (rpW1Class n)

/-- **The monodromy functional of `RPⁿ`** (Prompt 18 target), constructed from the
genuine first Stiefel–Whitney class of the double cover. Its invariance under the
homology pushforward of every descended odd map follows from
`rpW1Class_inducedOnRP_invariant` via naturality of the Kronecker pairing. -/
noncomputable def monodromyFunctional (n : ℕ) : MonodromyFunctional n where
  g := w1Functional n
  invariant := by
    intro f hf
    have hnat := kroneckerMap_naturality_apply (TopCat.ofHom (inducedOnRP f hf)) 1 (rpW1Class n)
    rw [rpW1Class_inducedOnRP_invariant n f hf] at hnat
    exact hnat.symm

/-- The canonical degree-one class `α = w₁ ∈ H¹(RPⁿ; F₂)`, now produced from the
genuine constructed monodromy functional. -/
noncomputable def rpAlphaW1 (n : ℕ) : rpCohomology n 1 :=
  rpAlpha n (monodromyFunctional n)

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
