import GroupApproximation.CharClass.RelativeLineHomotopy
import GroupApproximation.CharClass.LIXChartIso
import GroupApproximation.CharClass.LIXLocalPairClosed
import GroupApproximation.CharClass.MayerVietorisRestriction

/-!
# The neighbourhood the compatibility square is compared on

Lane `lix-hsq`.

`hsq`'s two routes reach the local model through **different** neighbourhoods of the
section's zero: the left one through `(lixBC dd).target`, which is where the base chart
lands, and the right one through `lixTrivBall`, which is where `cc-bundle`'s trivialisation
is defined.  `cc-lix-odd` landed the containment (`lixBaseBall_subset_target`), and this
file takes the step it was landed for: it names the corresponding neighbourhood of the
**origin of the local model** and shows that restricting to it loses nothing.

## Why the neighbourhood must be this one and not any small one

`lixTrivBall` is *by construction* the base chart's image of a **metric ball around the
origin** in chart coordinates (`LIXBaseBall`).  A metric ball around the origin is convex,
so it is star-shaped about the origin, and that is the only property of it the comparison
homotopy uses: the homotopy contracts a chart-coordinate point to the origin along the
segment and needs every intermediate point to stay where the section, the trivialisation
and the chart are all defined.  A neighbourhood produced by an abstract "small enough"
argument would not do, and the ball is not an implementation detail.

## Restricting to it loses nothing

Excision at the point identifies the relative group of `(ℂ^r, ℂ^r ∖ 0)` with that of every
open neighbourhood of the origin, so the restriction between two nested neighbourhoods is
an isomorphism and in particular injective.  That is `injective_relPullback_subInclusion`,
stated generically; the pair `(lixU, lixU ∖ 0)` then inherits the local model's one
dimensionality, which is what `RelativeLineHomotopy` consumes.

## Main definitions

* `lixHsqBall` — **the ball in chart coordinates**, with `lixTrivBall` its image.
* `lixU` — **its image in the local model**, an open neighbourhood of the origin.

## Main results

* `RelativeSupport.injective_relPullback_subInclusion` — restriction between two nested
  punctured neighbourhoods of a point is injective.
* `smul_mem_lixHsqBall` — the ball is star-shaped about the origin.
* `lixULine` — **the relative group of `(lixU, lixU ∖ 0)` in the top degree is a line.**
* `injective_lixShrink` — restricting from the chart's target to `lixU` is injective.
-/

noncomputable section

namespace GroupApproximation.CharClass

open Set CategoryTheory Limits
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

/-! ## 1. Restriction between nested punctured neighbourhoods -/

namespace RelativeSupport

/-- **Restricting a punctured pair to a smaller neighbourhood of the point is injective.**
Both neighbourhoods carry the relative group of the ambient punctured pair by excision at
the point, so the restriction between them is an isomorphism; only injectivity is used
downstream, so only injectivity is stated. -/
theorem injective_relPullback_subInclusion {X : TopCat.{0}} [T1Space X] (z : X)
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hzU : z ∈ U) (hzV : z ∈ V)
    (hUV : U ⊆ V)
    (hsub : ∀ x ∈ ((Subtype.val : ↥U → X) ⁻¹' ({z}ᶜ : Set X)),
      (ConcreteCategory.hom (subInclusion hUV)) x ∈
        ((Subtype.val : ↥V → X) ⁻¹' ({z}ᶜ : Set X)))
    (n : ℕ) : Function.Injective (relPullback (ZMod 2) (subInclusion hUV) hsub n).hom := by
  have hgV : ∀ y ∈ ((Subtype.val : ↥V → X) ⁻¹' ({z}ᶜ : Set X)),
      (ConcreteCategory.hom (sInclusion V)) y ∈ ({z}ᶜ : Set X) := fun _ hy => hy
  have hgU : ∀ y ∈ ((Subtype.val : ↥U → X) ⁻¹' ({z}ᶜ : Set X)),
      (ConcreteCategory.hom (sInclusion U)) y ∈ ({z}ᶜ : Set X) := fun _ hy => hy
  have hisoV : IsIso (relPullback (ZMod 2) (sInclusion V) hgV n) :=
    isIso_excision (pointComplementOpen X z) ⟨V, hV⟩ (pointComplement_sup z ⟨V, hV⟩ hzV) n
  have hisoU : IsIso (relPullback (ZMod 2) (sInclusion U) hgU n) :=
    isIso_excision (pointComplementOpen X z) ⟨U, hU⟩ (pointComplement_sup z ⟨U, hU⟩ hzU) n
  have hbV : Function.Bijective (relPullback (ZMod 2) (sInclusion V) hgV n).hom :=
    (ConcreteCategory.isIso_iff_bijective _).1 hisoV
  have hbU : Function.Bijective (relPullback (ZMod 2) (sInclusion U) hgU n).hom :=
    (ConcreteCategory.isIso_iff_bijective _).1 hisoU
  have hcomp : relPullback (ZMod 2) (sInclusion U) hgU n
      = relPullback (ZMod 2) (sInclusion V) hgV n
        ≫ relPullback (ZMod 2) (subInclusion hUV) hsub n :=
    relPullback_comp (ZMod 2) (subInclusion hUV) (sInclusion V) hsub hgV hgU n
  have hcompApply : ∀ a' : ↥(relCohomology (ZMod 2) X ({z}ᶜ : Set X) n),
      (relPullback (ZMod 2) (sInclusion U) hgU n).hom a'
        = (relPullback (ZMod 2) (subInclusion hUV) hsub n).hom
            ((relPullback (ZMod 2) (sInclusion V) hgV n).hom a') := by
    intro a'
    rw [hcomp]
    rfl
  intro a b hab
  obtain ⟨a', rfl⟩ := hbV.2 a
  obtain ⟨b', rfl⟩ := hbV.2 b
  refine congrArg (fun t => (relPullback (ZMod 2) (sInclusion V) hgV n).hom t) (hbU.1 ?_)
  rw [hcompApply a', hcompApply b', hab]

end RelativeSupport

/-! ## 2. The ball in chart coordinates -/

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ} {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ}

/-- The radius `lixTrivBall` was cut at. -/
def lixHsqEps (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) : ℝ :=
  lixBaseEps dd (lixTrivSet hGc hGu) (isOpen_lixTrivSet hGc hGu)
    (lixZero_mem_lixTrivSet hGc hGu)

/-- **The ball in chart coordinates**, of which `lixTrivBall` is the base chart's image. -/
def lixHsqBall (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    Set (ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) :=
  Metric.ball 0 (lixHsqEps hGc hGu)

theorem lixTrivBall_eq_image (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    lixTrivBall hGc hGu = (lixBC dd) '' lixHsqBall hGc hGu := rfl

theorem lixHsqBall_subset_bc_source (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    lixHsqBall hGc hGu ⊆ (lixBC dd).source :=
  fun _ hw => (lixBaseBallPre_subset (lixTrivSet hGc hGu) (isOpen_lixTrivSet hGc hGu)
    (lixZero_mem_lixTrivSet hGc hGu) hw).1

theorem lixHsqBall_subset_fc_source (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    lixHsqBall hGc hGu ⊆ (lixFC dd).source := by
  rw [← lixBC_source_eq_lixFC_source]
  exact lixHsqBall_subset_bc_source hGc hGu

theorem lixHsqEps_pos (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    0 < lixHsqEps (dd := dd) hGc hGu :=
  lixBaseEps_pos _ _ _

theorem zero_mem_lixHsqBall (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    (0 : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) ∈ lixHsqBall hGc hGu :=
  Metric.mem_ball_self (lixHsqEps_pos hGc hGu)

/-- **The ball is star-shaped about the origin.**  This is the only property of it the
comparison homotopy uses, and it is available because `lixTrivBall` was cut as a metric
ball in chart coordinates rather than by an abstract smallness argument. -/
theorem smul_mem_lixHsqBall (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    {q : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ)} (hq : q ∈ lixHsqBall hGc hGu)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : s • q ∈ lixHsqBall hGc hGu :=
  (convex_ball (0 : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) _).smul_mem_of_zero_mem
    (zero_mem_lixHsqBall hGc hGu) hq hs

/-! ## 3. Its image in the local model -/

/-- **The neighbourhood of the origin of the local model** the square is compared on. -/
def lixU (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    Set (Fin (lixRank dd) → ℂ) :=
  (lixFC dd) '' lixHsqBall hGc hGu

theorem isOpen_lixU (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    IsOpen (lixU hGc hGu) :=
  ((lixFC dd).isOpen_image_iff_of_subset_source
    (lixHsqBall_subset_fc_source hGc hGu)).mpr Metric.isOpen_ball

theorem zero_mem_lixU (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    (0 : Fin (lixRank dd) → ℂ) ∈ lixU hGc hGu :=
  ⟨(0, 0), zero_mem_lixHsqBall hGc hGu, lixFC_zero⟩

theorem lixU_subset_target (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    lixU hGc hGu ⊆ (lixFC dd).target := by
  rw [lixU, ← (lixFC dd).image_source_eq_target]
  exact Set.image_mono (lixHsqBall_subset_fc_source hGc hGu)

theorem symm_mem_lixHsqBall (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    {v : Fin (lixRank dd) → ℂ} (hv : v ∈ lixU hGc hGu) :
    (lixFC dd).symm v ∈ lixHsqBall hGc hGu := by
  obtain ⟨q, hq, rfl⟩ := hv
  rwa [(lixFC dd).left_inv (lixHsqBall_subset_fc_source hGc hGu hq)]

/-! ## 4. The pair over it is a line -/

/-- **The relative group of `(lixU, lixU ∖ 0)` in the top degree is a line**, by excision at
the origin against the local model. -/
def lixULine (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    ↥(relCohomology (ZMod 2) (TopCat.of ↥(lixU hGc hGu))
        ((Subtype.val : ↥(lixU hGc hGu) → (Fin (lixRank dd) → ℂ)) ⁻¹'
          ({0}ᶜ : Set (Fin (lixRank dd) → ℂ))) (2 * lixRank dd)) ≃ₗ[ZMod 2] ZMod 2 :=
  ((excisionIsoPoint (TopCat.of (Fin (lixRank dd) → ℂ)) 0 (lixU hGc hGu)
      (isOpen_lixU hGc hGu) (zero_mem_lixU hGc hGu)
      (2 * lixRank dd)).symm).toLinearEquiv.trans (localEquiv (lixRank dd))

/-! ## 5. Restricting from the chart's target to it -/

/-- The inclusion of `lixU` into the chart's target, with the ambient pinned as a `TopCat`:
`subInclusion` takes it implicitly and cannot recover it from a `Set` of a plain type. -/
def lixShrinkMap (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    TopCat.of ↥(lixU hGc hGu) ⟶ TopCat.of ↥(lixFC dd).target :=
  subInclusion (X := TopCat.of (Fin (lixRank dd) → ℂ)) (lixU_subset_target hGc hGu)

theorem lixShrink_mapsTo (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    ∀ x ∈ ((Subtype.val : ↥(lixU hGc hGu) → (Fin (lixRank dd) → ℂ)) ⁻¹'
        ({0}ᶜ : Set (Fin (lixRank dd) → ℂ))),
      (ConcreteCategory.hom (lixShrinkMap hGc hGu)) x ∈
        ((Subtype.val : ↥(lixFC dd).target → (Fin (lixRank dd) → ℂ)) ⁻¹'
          ({0}ᶜ : Set (Fin (lixRank dd) → ℂ))) :=
  fun _ hx => hx

/-- **Restricting from the chart's target to `lixU` is injective**, so an equation between
two maps into the chart's target may be checked on `lixU`. -/
theorem injective_lixShrink (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    Function.Injective (relPullback (ZMod 2) (lixShrinkMap hGc hGu)
      (lixShrink_mapsTo hGc hGu) (2 * lixRank dd)).hom :=
  RelativeSupport.injective_relPullback_subInclusion
    (X := TopCat.of (Fin (lixRank dd) → ℂ)) (0 : Fin (lixRank dd) → ℂ)
    (isOpen_lixU hGc hGu) (lixFC dd).open_target (zero_mem_lixU hGc hGu)
    zero_mem_lixFC_target (lixU_subset_target hGc hGu) (lixShrink_mapsTo hGc hGu)
    (2 * lixRank dd)

end GroupApproximation.CharClass
