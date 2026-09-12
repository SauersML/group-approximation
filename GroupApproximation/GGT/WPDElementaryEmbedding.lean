import GroupApproximation.GGT.ElementaryClosure
import GroupApproximation.GGT.HullSCConeOff
import GroupApproximation.GGT.WPDAcylindricalHyperbolicity

/-!
# Dahmani--Guirardel--Osin's Theorem 6.8: the plan, and the reduction

`GGT.DGOTheorem68` is the implication `(AH₃) ⇒ (AH₄)` of Osin's Theorem 1.2:

> a loxodromic WPD element lies in a proper hyperbolically embedded subgroup.

This module fixes the shape of the proof, proves the parts that are not
geometry, and leaves **one** named geometric proposition.  It does not prove
Theorem 6.8.

## The four obligations

Take `E := Elementary.elementaryClosure D.elt` --- Osin's `E(g)`, the elements
conjugating a nonzero power of `g` to a nonzero power of `g`.  Then
`DGOTheorem68` asks for

* (i)   `D.elt ∈ E` --- `Elementary.self_mem_elementaryClosure`, proved;
* (ii)  `E ≠ ⊤`;
* (iii) `Γ(G, X ⊔ E)` hyperbolic, for a base `X` of one's choice;
* (iv)  every relative ball `d̂_E(1, ·) ≤ n` finite,

where (iii) and (iv) are the two fields of
`GGT.RelGenSet.IsHyperbolicallyEmbedded` for `HullSC.coneOff X E`, and
`HullSC.isHypEmbeddedOf_coneOff` turns them into `IsHypEmbedded G E`.
`dgoTheorem68_of` is that assembly: it takes (ii) and (iii)+(iv) as the two
named propositions `ElementaryClosureProper` and
`ElementaryConeOffHypEmbedded` and proves `DGOTheorem68`.

**(iii) and (iv) are coupled through `X` and cannot be split between two
lanes.**  Enlarging `X` helps (iii) and hurts (iv): `HullSC.coneOff` is one
relative generating set, and both fields speak about it.  So the named
proposition below existentially quantifies `X` and carries both fields.

## The plan for the geometry

The corrected `AH3Data` carries the source convention that its hyperbolic
space is geodesic.  The proof therefore works directly on `D.Space`; passing
to the orbit pseudo-metric would destroy geodesicity and is neither needed nor
valid.

For a scale `C`, the natural base is the displacement ball
`{a | d(x₀, a·x₀) ≤ C}`.  It is symmetric
(`displacementBall_inv_mem`) and generates as soon as it contains a generating
set (`displacementBall_isSymmetricGeneratingSet`).  The remaining geometry is
Dahmani--Guirardel--Osin §4: hyperbolicity of the coned-off graph and finiteness
of relative balls follow by tracing relative words away from and back to the
loxodromic quasi-axis, then applying WPD.

## Two traps, both already refuted in the repository

* `GGT.not_isHypEmbeddedOf_of_subset`: an infinite `E` inside the base is never
  hyperbolically embedded over it.  `E` is infinite here
  (`infinite_elementaryClosure`), so the cheap route --- take `X = G`, where
  `Γ(G, X ⊔ E)` has diameter one and is hyperbolic by
  `isHyperbolicSpace_of_bounded` --- is closed, and `not_isHypEmbeddedOf_univ`
  records that.  The base must be thin enough that `E` is not shortcuttable.
* `GGT.RelGenSet.not_isLoxodromic_of_mem_fam`: no element of `E` is loxodromic
  on `Γ(G, X ⊔ E)`.  Thus every use of loxodromy of `g` belongs to the original
  geodesic `AH3Data` space, never to the cone-off.

## A note on (ii), for whoever discharges it

`E ≠ ⊤` does **not** follow from `¬ IsVirtuallyCyclic G` by way of
`GGT.actsNonElementarily_of_no_common_power`: that route needs a pair of
elements with no common nonzero power, and a group can be non-virtually-cyclic
without having one.  A Tarski monster of exponent `p` is infinite, torsion --- so
not virtually cyclic --- and any two of its elements satisfy `a^p = b^p = 1`.
The `(AH₃)` datum has to be used, not just the non-virtual-cyclicity: what rules
the monster out is that it has no element of infinite order, hence no loxodromic
one.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-! ## Bounded spaces are hyperbolic -/

/-- **A space of diameter at most `C` is `C`-hyperbolic.**  Every Gromov product
is at most `C` and every Gromov product is nonnegative, so the four-point
condition holds with nothing to check.

This is what makes the degenerate base `X = G` hyperbolic, and it is the reason
the base cannot be chosen that way: the local finiteness clause then fails, by
`not_isHypEmbeddedOf_univ`. -/
theorem isHyperbolicSpace_of_bounded {X : Type v} [PseudoMetricSpace X] {C : ℝ}
    (hC : ∀ p q : X, dist p q ≤ C) : IsHyperbolicSpace C X := by
  intro w x y z
  have hxy : gromovProduct x y w ≤ C := by
    have h1 := hC x w
    have h2 := hC y w
    have h3 : (0 : ℝ) ≤ dist x y := dist_nonneg
    unfold gromovProduct
    linarith
  have hnn := gromovProduct_nonneg x z w
  have hmin : min (gromovProduct x y w) (gromovProduct y z w) ≤ C :=
    le_trans (min_le_left _ _) hxy
  linarith

/-- **The base cannot be everything.**  An infinite subgroup is not
hyperbolically embedded over a base containing it, and `Set.univ` contains it.
So the fact that coning off everything makes the relative Cayley graph bounded,
hence hyperbolic, is of no use. -/
theorem not_isHypEmbeddedOf_univ {G : Type u} [Group G] {H : Subgroup G}
    (hinf : (H : Set G).Infinite) :
    ¬ IsHypEmbeddedOf G (Set.univ : Set G) H :=
  not_isHypEmbeddedOf_of_subset (Set.subset_univ _) hinf

/-! ## The displacement ball, the base of the cone-off -/

section Ball

/-- **The `C`-displacement ball** `{a | d(x₀, a·x₀) ≤ C}`, the base to cone off
`E(g)` over. -/
def displacementBall {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
    [MulAction G X] (x₀ : X) (C : ℝ) : Set G := {a : G | dist x₀ (a • x₀) ≤ C}

theorem mem_displacementBall {G : Type u} [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] {x₀ : X} {C : ℝ} {a : G} :
    a ∈ displacementBall (G := G) x₀ C ↔ dist x₀ (a • x₀) ≤ C := Iff.rfl

/-- **The displacement ball is symmetric.**  Moving the basepoint by `a⁻¹` costs
what moving it by `a` costs, because the action is isometric. -/
theorem displacementBall_inv_mem {G : Type u} [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] (hiso : IsIsometricAction G X) (x₀ : X)
    (C : ℝ) {a : G} (ha : a ∈ displacementBall (G := G) x₀ C) :
    a⁻¹ ∈ displacementBall (G := G) x₀ C := by
  have h : dist (a • x₀) (a • (a⁻¹ • x₀)) = dist x₀ (a⁻¹ • x₀) :=
    hiso a x₀ (a⁻¹ • x₀)
  rw [smul_inv_smul] at h
  show dist x₀ (a⁻¹ • x₀) ≤ C
  rw [← h, dist_comm]
  exact ha

/-- **The displacement ball is an alphabet as soon as it contains a generating
set.**  For a finitely generated `G` this holds for every `C` past the largest
displacement of a finite generating set, so the base of the cone-off is a
genuine `Alphabet G`. -/
theorem displacementBall_isSymmetricGeneratingSet {G : Type u} [Group G]
    {X : Type v} [PseudoMetricSpace X] [MulAction G X]
    (hiso : IsIsometricAction G X)
    (x₀ : X) (C : ℝ) {Y : Set G} (hY : Subgroup.closure Y = ⊤)
    (hYC : Y ⊆ displacementBall (G := G) x₀ C) :
    IsSymmetricGeneratingSet (displacementBall (G := G) x₀ C) := by
  refine ⟨fun a ha => displacementBall_inv_mem hiso x₀ C ha, ?_⟩
  refine eq_top_iff.mpr ?_
  rw [← hY]
  exact Subgroup.closure_mono hYC

end Ball

/-! ## The elementary closure is infinite -/

/-- **`E(g)` is infinite when `g` is loxodromic.**  It contains `g`, whose order
is infinite.  This is what makes the trap of `not_isHypEmbeddedOf_univ` fire,
and it is the infinitude clause `(AH₄)` asks for. -/
theorem infinite_elementaryClosure {G : Type u} [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] {g : G} {x : X}
    (hlox : IsLoxodromic g x) :
    ((Elementary.elementaryClosure g : Subgroup G) : Set G).Infinite :=
  infinite_of_mem_of_isLoxodromic hlox (Elementary.self_mem_elementaryClosure g)

/-! ## The two named obligations, and the assembly -/

/-- **The geometry of Dahmani--Guirardel--Osin's Theorem 6.8**: over a suitable
base the elementary closure of a loxodromic WPD element is hyperbolically
embedded.

Both fields of `IsHyperbolicallyEmbedded` are here, and deliberately so: they
are statements about one and the same relative generating set, and enlarging the
base helps the first and hurts the second. -/
def ElementaryConeOffHypEmbedded : Prop :=
  ∀ (G : Type u) [Group G] (D : AH3Data.{u, v} G), ¬ IsVirtuallyCyclic G →
    ∃ X : Alphabet G,
      (HullSC.coneOff X (Elementary.elementaryClosure D.elt)).IsHyperbolicallyEmbedded

/-- **The elementary closure of a loxodromic WPD element is a proper subgroup.**
Dahmani--Guirardel--Osin prove it by way of `E(g)` being virtually cyclic, which
`¬ IsVirtuallyCyclic G` then contradicts; the repository's partial machinery for
it is `Elementary.exists_notMem_elementaryClosure_of_centralizer`.  It is not a
formal consequence of `¬ IsVirtuallyCyclic G` alone --- see the note in the
module docstring. -/
def ElementaryClosureProper : Prop :=
  ∀ (G : Type u) [Group G] (D : AH3Data.{u, v} G), ¬ IsVirtuallyCyclic G →
    Elementary.elementaryClosure D.elt ≠ ⊤

/-- **Theorem 6.8 from the two obligations.**  The subgroup is the elementary
closure; membership is `self_mem_elementaryClosure`; properness is the second
obligation; and the hyperbolic embedding is the cone-off of the first, through
`HullSC.isHypEmbeddedOf_coneOff`. -/
theorem dgoTheorem68_of (hcone : ElementaryConeOffHypEmbedded.{u, v})
    (hproper : ElementaryClosureProper.{u, v}) : DGOTheorem68.{u, v} := by
  intro G _ D hvc
  obtain ⟨X, hX⟩ := hcone G D hvc
  have hne := hproper G D hvc
  exact ⟨Elementary.elementaryClosure D.elt,
    Elementary.self_mem_elementaryClosure D.elt, hne,
    (HullSC.isHypEmbeddedOf_coneOff X (Elementary.elementaryClosure D.elt)
      hX).isHypEmbedded⟩

end GGT
end GroupApproximation
