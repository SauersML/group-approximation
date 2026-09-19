import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.Covering
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CohomologyCupProduct
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.AlexanderWhitneyFaceMaps
import Mathlib

/-!
# The first Stiefel–Whitney cocycle `w₁` of `RPⁿ` from the double cover

This file builds, **genuinely and build-clean**, the degree-one singular `F₂`
cocycle of `RPⁿ` representing the first Stiefel–Whitney class `w₁` of the
canonical double cover `proj n : Sⁿ → RPⁿ`, by lifting singular simplices to the
sphere.

The construction is the honest geometric one:

* a (set-theoretic) section `rpSection n` of `proj n` (`RPnW1Cochain` covering
  core, also reused);
* every singular `k`-simplex `σ : |Δᵏ| → RPⁿ` lifts to `Sⁿ` (the topological
  simplex is convex, hence simply connected and locally path connected), giving
  `simplexLift`;
* the **sheet parity** `sheetParity` of a sphere point measures whether it agrees
  with the chosen section over its image;
* the cochain value `w1Value σ` of a `1`-simplex is the sum of the sheet parities
  of (any) lift at the two endpoints — independent of the lift because flipping
  the lift flips both parities (`sheetParity_neg`);
* assembled into a genuine `1`-cochain `w1Cochain`, which is a **cocycle**
  (`w1Cochain_cocycle`): the boundary of every singular `2`-simplex lifts to the
  sphere, and the three edge-parities of a triangle cancel mod 2.

## Main declarations

* covering core: `rpSection`, `proj_rpSection`, `proj_neg_comp_lift`,
  `proj_lift_of_simplyConnected`, `proj_lift_dichotomy`;
* `sheetParity`, `sphere_ne_neg`, `sheetParity_neg`;
* `rpCochainSimplexMap`, `simplexLift`, `simplexLift_spec`;
* `w1Value`, `w1Cochain`, `w1Cochain_eval`;
* `rpCochainSimplexMap_face`, `toTop_delta_vertex`, `w1Value_face`;
* `w1Cochain_cocycle` — the cocycle property;
* `rpW1Class` — the resulting genuine class in `H¹(RPⁿ; F₂)`.
-/

open CategoryTheory AlgebraicTopology Limits
  GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-! ## 1. Covering-theoretic core -/

/-- A (set-theoretic) section of the double cover `proj n : Sⁿ → RPⁿ`, choosing for
each point of `RPⁿ` one of its two preimages on the sphere. -/
noncomputable def rpSection (n : ℕ) : RP n → Sphere n := fun q => q.out

/-- `rpSection n` is a section of `proj n`. -/
theorem proj_rpSection (n : ℕ) (q : RP n) : proj n (rpSection n q) = q :=
  Quotient.out_eq q

/-- The antipode of a lift is again a lift. -/
theorem proj_neg_comp_lift (n : ℕ) {A : Type} [TopologicalSpace A]
    {f : C(A, RP n)} {g : C(A, Sphere n)} (h : (proj n) ∘ g = f) :
    (proj n) ∘ ((antipodal n).comp g) = f := by
  ext x
  show proj n (-(g x)) = f x
  rw [proj_neg]
  exact congrFun h x

/-- **The covering lifting criterion for `proj n`.** Every continuous map `f` from
a path-connected, locally path-connected, simply connected space `A` into `RPⁿ`
lifts to a continuous map `g : A → Sⁿ` with `proj n ∘ g = f`, normalised so that
`g a₀ = rpSection n (f a₀)` at a chosen base point `a₀`. -/
theorem proj_lift_of_simplyConnected (n : ℕ) {A : Type} [TopologicalSpace A]
    [PathConnectedSpace A] [LocallyPathConnectedSpace A] [SimplyConnectedSpace A]
    (f : C(A, RP n)) (a₀ : A) :
    ∃ g : C(A, Sphere n), (proj n) ∘ g = f ∧ g a₀ = rpSection n (f a₀) := by
  have he : proj n (rpSection n (f a₀)) = f a₀ := proj_rpSection n (f a₀)
  have hsub : Subsingleton (FundamentalGroup A a₀) :=
    SimplyConnectedSpace.instSubsingletonQuotient a₀ a₀
  have hrange : (FundamentalGroup.map f a₀).range ≤
      (FundamentalGroup.mapOfEq ⟨proj n, (proj n).continuous⟩ he).range := by
    rw [show (FundamentalGroup.map f a₀).range = ⊥ from ?_]
    · exact bot_le
    · rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      obtain ⟨y, rfl⟩ := hx
      rw [Subsingleton.elim y 1, map_one]
  obtain ⟨F, ⟨hF1, hF2⟩, _⟩ :=
    (proj_isCoveringMap n).existsUnique_continuousMap_lifts_of_range_le he hrange
  exact ⟨F, hF2, hF1⟩

/-- **Uniqueness of lifts up to the deck involution.** On a (nonempty) preconnected
domain `A`, any two lifts `g₁, g₂ : A → Sⁿ` of the same map `f : A → RPⁿ` are
either equal or globally antipodal. -/
theorem proj_lift_dichotomy (n : ℕ) {A : Type} [TopologicalSpace A]
    [PreconnectedSpace A] [Nonempty A] {f : C(A, RP n)} (g₁ g₂ : C(A, Sphere n))
    (h1 : (proj n) ∘ g₁ = f) (h2 : (proj n) ∘ g₂ = f) :
    g₁ = g₂ ∨ ∀ a, g₁ a = -(g₂ a) := by
  obtain ⟨a₀⟩ := ‹Nonempty A›
  have hpt : proj n (g₁ a₀) = proj n (g₂ a₀) := by
    have := congrFun (h1.trans h2.symm) a₀; simpa using this
  rw [proj_eq_iff] at hpt
  rcases hpt with h | h
  · left
    have hc : (proj n) ∘ g₁ = (proj n) ∘ g₂ := by rw [h1, h2]
    exact ContinuousMap.ext
      (congrFun ((proj_isCoveringMap n).eq_of_comp_eq g₁.continuous g₂.continuous hc a₀ h))
  · right
    intro a
    let g₂' : C(A, Sphere n) := (antipodal n).comp g₂
    have hcomp : (proj n) ∘ g₂' = f := proj_neg_comp_lift n h2
    have heq : g₁ = g₂' := by
      have hc : (proj n) ∘ g₁ = (proj n) ∘ g₂' := by rw [h1, hcomp]
      have hpt2 : g₁ a₀ = g₂' a₀ := h
      exact ContinuousMap.ext
        (congrFun ((proj_isCoveringMap n).eq_of_comp_eq g₁.continuous g₂'.continuous hc a₀ hpt2))
    rw [heq]; rfl

/-! ## 2. Topological-simplex instances -/

/-- The topological `k`-simplex is locally path connected (it is convex). -/
instance simplexLocPathConnected (k : ℕ) :
    LocallyPathConnectedSpace (SimplexCategory.toTop.obj (SimplexCategory.mk k)) := by
  haveI : LocallyPathConnectedSpace (stdSimplex ℝ (Fin (k + 1))) :=
    (convex_stdSimplex ℝ (Fin (k + 1))).locallyPathConnectedSpace
  exact (Homeomorph.ulift (X := stdSimplex ℝ (Fin (k + 1)))).isOpenEmbedding.locallyPathConnectedSpace

/-- The topological `k`-simplex is contractible (it is convex and nonempty). -/
instance simplexContractible (k : ℕ) :
    ContractibleSpace (SimplexCategory.toTop.obj (SimplexCategory.mk k)) := by
  haveI : ContractibleSpace (stdSimplex ℝ (Fin (k + 1))) :=
    (convex_stdSimplex ℝ (Fin (k + 1))).contractibleSpace (Set.nonempty_coe_sort.mp inferInstance)
  exact (Homeomorph.ulift (X := stdSimplex ℝ (Fin (k + 1)))).contractibleSpace

/-! ## 3. Sheet parity -/

/-- The **sheet parity** of a sphere point `p`: `0` if `p` is the chosen section
value over `proj n p`, and `1` if it is the antipodal preimage. -/
def sheetParity (n : ℕ) (p : Sphere n) : ZMod 2 :=
  if p = rpSection n (proj n p) then 0 else 1

/-- A sphere point is never equal to its antipode. -/
theorem sphere_ne_neg (n : ℕ) (p : Sphere n) : p ≠ -p := by
  intro h
  have hv : (p : EuclideanSpace ℝ (Fin (n + 1))) = -(p : EuclideanSpace ℝ (Fin (n + 1))) := by
    have := congrArg Subtype.val h; simpa using this
  have h0 : (p : EuclideanSpace ℝ (Fin (n + 1))) = 0 := by
    have : (2 : ℝ) • (p : EuclideanSpace ℝ (Fin (n + 1))) = 0 := by
      rw [two_smul]; nth_rewrite 1 [hv]; abel
    simpa using this
  have hp := p.2
  rw [Metric.mem_sphere, dist_zero_right, h0] at hp
  simp at hp

/-- **The flip law for sheet parity**: passing to the antipode toggles the parity. -/
theorem sheetParity_neg (n : ℕ) (p : Sphere n) : sheetParity n (-p) = sheetParity n p + 1 := by
  have hpr : proj n (-p) = proj n p := proj_neg p
  set s := rpSection n (proj n p) with hs
  have hsfib : proj n s = proj n p := by rw [hs, proj_rpSection]
  have hcases : s = p ∨ s = -p := (proj_eq_iff (n := n) (x := p) (y := s)).mp hsfib
  unfold sheetParity
  rw [hpr]
  rcases hcases with hsp | hsn
  · have h1 : p = s := hsp.symm
    have h2 : ¬ (-p = s) := by rw [hsp]; intro h; exact (sphere_ne_neg n p) h.symm
    rw [if_pos h1, if_neg h2]; decide
  · have h1 : ¬ (p = s) := by rw [hsn]; intro h; exact (sphere_ne_neg n p) h
    have h2 : (-p = s) := hsn.symm
    rw [if_neg h1, if_pos h2]; decide

/-! ## 4. The lift of a singular simplex -/

/-- The continuous map `|Δᵏ| → RPⁿ` underlying a singular `k`-simplex of `RPⁿ`. -/
def rpCochainSimplexMap (n k : ℕ) (σ : singularSimplices (TopCat.of (RP n)) k) :
    C(SimplexCategory.toTop.obj (SimplexCategory.mk k), RP n) :=
  (σ.down).hom

/-- A continuous lift `|Δᵏ| → Sⁿ` of a singular `k`-simplex `σ` (the topological
simplex is convex, hence simply connected, so `proj_lift_of_simplyConnected`
applies). -/
def simplexLift (n k : ℕ) (σ : singularSimplices (TopCat.of (RP n)) k) :
    C(SimplexCategory.toTop.obj (SimplexCategory.mk k), Sphere n) :=
  Classical.choose (proj_lift_of_simplyConnected n (rpCochainSimplexMap n k σ)
    (ULift.up (stdSimplex.vertex 0)))

/-- `simplexLift n k σ` is a lift of `rpCochainSimplexMap n k σ`. -/
theorem simplexLift_spec (n k : ℕ) (σ : singularSimplices (TopCat.of (RP n)) k) :
    (proj n) ∘ (simplexLift n k σ) = rpCochainSimplexMap n k σ :=
  (Classical.choose_spec (proj_lift_of_simplyConnected n (rpCochainSimplexMap n k σ)
    (ULift.up (stdSimplex.vertex 0)))).1

/-- The `j`-th vertex of the topological `k`-simplex. -/
def simplexVertex (k : ℕ) (j : Fin (k + 1)) :
    (SimplexCategory.toTop.obj (SimplexCategory.mk k) : Type) :=
  ULift.up (stdSimplex.vertex j)

/-! ## 5. The `w₁` cochain -/

/-- The **`w₁` value** of a singular `1`-simplex `σ`: the sum of the sheet parities
of a lift of `σ` at the two endpoints. (Independent of the lift, by
`sheetParity_neg`.) -/
def w1Value (n : ℕ) (σ : singularSimplices (TopCat.of (RP n)) 1) : ZMod 2 :=
  sheetParity n (simplexLift n 1 σ (simplexVertex 1 0))
    + sheetParity n (simplexLift n 1 σ (simplexVertex 1 1))

/-- The **`w₁` cochain** of `RPⁿ`, the genuine singular `1`-cochain assembling the
`w1Value`s. -/
def w1Cochain (n : ℕ) : singularCochainGroup (ZMod 2) (TopCat.of (RP n)) 1 :=
  Sigma.desc (fun (σ : singularSimplices (TopCat.of (RP n)) 1) =>
    ModuleCat.ofHom ((w1Value n σ) • (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2)))

/-- The defining evaluation of `w1Cochain`. -/
theorem w1Cochain_eval (n : ℕ) (σ : singularSimplices (TopCat.of (RP n)) 1) :
    cochainEval 1 (w1Cochain n) σ = w1Value n σ := by
  change ModuleCat.Hom.hom (Sigma.ι (fun (_ : singularSimplices (TopCat.of (RP n)) 1) =>
      ModuleCat.of (ZMod 2) (ZMod 2)) σ ≫
    Sigma.desc (fun (ρ : singularSimplices (TopCat.of (RP n)) 1) =>
      ModuleCat.ofHom ((w1Value n ρ) •
        (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2)))) (1 : ZMod 2) = _
  rw [Sigma.ι_desc]
  simp

/-! ## 6. The cocycle property -/

/-- A boundary face of a singular `2`-simplex, as a continuous map, is the simplex
precomposed with the geometric face inclusion `|Δ¹| → |Δ²|`. -/
theorem rpCochainSimplexMap_face (n : ℕ) (i : Fin 3) (σ : singularSimplices (TopCat.of (RP n)) 2) :
    rpCochainSimplexMap n 1 (faceSimplex (TopCat.of (RP n)) 1 i σ)
      = (rpCochainSimplexMap n 2 σ).comp (SimplexCategory.toTop.map (SimplexCategory.δ i)).hom := by
  unfold rpCochainSimplexMap faceSimplex; ext t; rfl

/-- The geometric face inclusion `δ i : |Δ¹| → |Δ²|` sends the `j`-th vertex to the
`(δ i j)`-th vertex. -/
theorem toTop_delta_vertex (i : Fin 3) (j : Fin 2) :
    (SimplexCategory.toTop.map (SimplexCategory.δ i)).hom (simplexVertex 1 j)
      = simplexVertex 2 (Fin.succAbove i j) := by
  rw [SimplexCategory.toTop_map]
  show ULift.up (stdSimplex.map _ (stdSimplex.vertex j))
    = ULift.up (stdSimplex.vertex (Fin.succAbove i j))
  rw [stdSimplex.map_vertex]; congr 1

/-- **The `w₁` value of a boundary face**, expressed through the global lift of the
ambient `2`-simplex: it is the sum of the sheet parities at the two endpoint
vertices of the edge. The lift ambiguity cancels mod 2 (`sheetParity_neg`). -/
theorem w1Value_face (n : ℕ) (i : Fin 3) (σ : singularSimplices (TopCat.of (RP n)) 2) :
    w1Value n (faceSimplex (TopCat.of (RP n)) 1 i σ)
      = sheetParity n (simplexLift n 2 σ (simplexVertex 2 (Fin.succAbove i 0)))
        + sheetParity n (simplexLift n 2 σ (simplexVertex 2 (Fin.succAbove i 1))) := by
  set face := faceSimplex (TopCat.of (RP n)) 1 i σ with hface
  set G := simplexLift n 2 σ with hG
  set L := simplexLift n 1 face with hL
  let Gd : C(SimplexCategory.toTop.obj (SimplexCategory.mk 1), Sphere n) :=
    G.comp (SimplexCategory.toTop.map (SimplexCategory.δ i)).hom
  have hGd : (proj n) ∘ Gd = rpCochainSimplexMap n 1 face := by
    have hGspec : (proj n) ∘ G = rpCochainSimplexMap n 2 σ := simplexLift_spec n 2 σ
    rw [rpCochainSimplexMap_face]; ext t
    show (proj n) (G ((SimplexCategory.toTop.map (SimplexCategory.δ i)).hom t)) = _
    exact congrFun hGspec ((SimplexCategory.toTop.map (SimplexCategory.δ i)).hom t)
  have hLspec : (proj n) ∘ L = rpCochainSimplexMap n 1 face := simplexLift_spec n 1 face
  have hdich := proj_lift_dichotomy n L Gd hLspec hGd
  have e0 : Gd (simplexVertex 1 0) = G (simplexVertex 2 (Fin.succAbove i 0)) := by
    show G ((SimplexCategory.toTop.map (SimplexCategory.δ i)).hom (simplexVertex 1 0)) = _
    rw [toTop_delta_vertex]
  have e1 : Gd (simplexVertex 1 1) = G (simplexVertex 2 (Fin.succAbove i 1)) := by
    show G ((SimplexCategory.toTop.map (SimplexCategory.δ i)).hom (simplexVertex 1 1)) = _
    rw [toTop_delta_vertex]
  have hval : w1Value n face
      = sheetParity n (L (simplexVertex 1 0)) + sheetParity n (L (simplexVertex 1 1)) := rfl
  rw [hval]
  rcases hdich with heq | hanti
  · rw [heq, e0, e1]
  · rw [hanti (simplexVertex 1 0), hanti (simplexVertex 1 1), e0, e1, sheetParity_neg,
      sheetParity_neg]
    have key : ∀ a b : ZMod 2, a + 1 + (b + 1) = a + b := by decide
    exact key _ _

/-- **The `w₁` cochain is a cocycle.** For every singular `2`-simplex, the three
edge parities of the triangle cancel mod 2. -/
theorem w1Cochain_cocycle (n : ℕ) :
    cochainCoboundary (ZMod 2) (TopCat.of (RP n)) 1 (w1Cochain n) = 0 := by
  apply cochain_ext
  intro σ
  rw [cochainEval_zero, cochainCoboundary_eval, Fin.sum_univ_three]
  rw [w1Cochain_eval, w1Cochain_eval, w1Cochain_eval, w1Value_face, w1Value_face, w1Value_face]
  have s00 : Fin.succAbove (0 : Fin 3) (0 : Fin 2) = 1 := by decide
  have s01 : Fin.succAbove (0 : Fin 3) (1 : Fin 2) = 2 := by decide
  have s10 : Fin.succAbove (1 : Fin 3) (0 : Fin 2) = 0 := by decide
  have s11 : Fin.succAbove (1 : Fin 3) (1 : Fin 2) = 2 := by decide
  have s20 : Fin.succAbove (2 : Fin 3) (0 : Fin 2) = 0 := by decide
  have s21 : Fin.succAbove (2 : Fin 3) (1 : Fin 2) = 1 := by decide
  simp only [s00, s01, s10, s11, s20, s21]
  generalize sheetParity n (simplexLift n 2 σ (simplexVertex 2 0)) = c0
  generalize sheetParity n (simplexLift n 2 σ (simplexVertex 2 1)) = c1
  generalize sheetParity n (simplexLift n 2 σ (simplexVertex 2 2)) = c2
  revert c0 c1 c2; decide

/-! ## 7. The `w₁` cohomology class -/

/-- **The first Stiefel–Whitney class** `w₁ ∈ H¹(RPⁿ; F₂)` of the canonical double
cover, as a genuine class in the project's singular cohomology. -/
def rpW1Class (n : ℕ) : cohomologyZMod2 (TopCat.of (RP n)) 1 :=
  cocycleClass (TopCat.of (RP n)) 1 (w1Cochain n) (w1Cochain_cocycle n)

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
