import GroupApproximation.GGT.HyperbolicAdditiveTransfer
import GroupApproximation.GGT.WPDElement

/-!
# Weak proper discontinuity transfers along a map of bounded additive distortion

`GGT/HyperbolicAdditiveTransfer.lean` moves `IsHyperbolicSpace`, `IsLoxodromic`,
`Independent` and `IsAcylindrical` along an equivariant map that changes every
distance by at most `C`.  This module adds the remaining predicate of
`GGT/WPDElement.lean`, weak proper discontinuity, which is the field
`AH3Data.wpd` of `GGT/WPDAcylindricalHyperbolicity.lean`.

The whole content is one inclusion of `ε`-stabilisers, `pairStab_subset_map`:
an element moving `x` and `y` by at most `ε` moves `f x` and `f y` by at most
`ε + C`, and conversely.  Weak proper discontinuity is a finiteness statement
about those sets and a subset of a finite set is finite, so both directions come
out at once, with the same power `M` and the cost `ε ↦ ε + C`.

## Why this is the case that matters

The relative Cayley graph of a group with respect to a peripheral subgroup and
the associated Bass--Serre tree are quasi-isometric with multiplicative constant
**one** --- the comparison map is `g ↦ g · ι(P)`, and the two metrics differ by
a bounded additive amount, not by a bounded ratio.  So the Morse lemma is not
needed to compare them, and neither `MorseLemmaStatement` nor
`QuasiIsometryHyperbolicityStatement` is invoked anywhere below: the additive
transfer already covers the comparison that Osin's Theorem 1.2 consumes.

One consequence is worth stating because it is a constraint rather than a tool.
Acylindricity transfers along the *same* map, in both directions
(`isAcylindrical_of_additiveDistortion` and its dense converse).  So a space of
bounded additive distortion from a tree is acylindrical exactly when the tree
action is: the pair cannot be split into an acylindrical tree and a
non-acylindrical Cayley graph.  If a construction needs the Cayley graph to fail
acylindricity, the tree action fails it too, which is precisely why the
Minasyan--Osin route runs on WPD rather than on acylindricity, and why the
lemmas here are the ones it needs.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry

universe u v w

section Transfer

variable {G : Type u} [Group G] {X : Type v} {Y : Type w}
  [PseudoMetricSpace X] [PseudoMetricSpace Y] [MulAction G X] [MulAction G Y]

/-- **The `ε`-stabiliser of a pair pushes into the `(ε + C)`-stabiliser of its
image.** -/
theorem pairStab_subset_map {C ε : ℝ} {f : X → Y}
    (hf : HasAdditiveDistortion C f) (hequiv : IsEquivariant G f) (x y : X) :
    pairStab G ε x y ⊆ pairStab G (ε + C) (f x) (f y) := by
  intro a ha
  rw [mem_pairStab] at ha
  obtain ⟨h1, h2⟩ := ha
  have e1 := hf x (a • x)
  have e2 := hf y (a • y)
  rw [hequiv a x] at e1
  rw [hequiv a y] at e2
  have e1b := (abs_le.mp e1).2
  have e2b := (abs_le.mp e2).2
  rw [mem_pairStab]
  exact ⟨by linarith, by linarith⟩

/-- **And the `ε`-stabiliser of the image pulls back to the `(ε + C)`-stabiliser
of the pair.** -/
theorem pairStab_map_subset {C ε : ℝ} {f : X → Y}
    (hf : HasAdditiveDistortion C f) (hequiv : IsEquivariant G f) (x y : X) :
    pairStab G ε (f x) (f y) ⊆ pairStab G (ε + C) x y := by
  intro a ha
  rw [mem_pairStab] at ha
  obtain ⟨h1, h2⟩ := ha
  have e1 := hf x (a • x)
  have e2 := hf y (a • y)
  rw [hequiv a x] at e1
  rw [hequiv a y] at e2
  have e1a := (abs_le.mp e1).1
  have e2a := (abs_le.mp e2).1
  rw [mem_pairStab]
  exact ⟨by linarith, by linarith⟩

/-- **Weak proper discontinuity pulls back** along an equivariant map of
additive distortion: the same power `M` works, and the `∀ ε` quantifier absorbs
the inflation `ε ↦ ε + C`. -/
theorem isWPDAt_of_map {C : ℝ} (hC : 0 ≤ C) {f : X → Y}
    (hf : HasAdditiveDistortion C f) (hequiv : IsEquivariant G f) {g : G}
    {x : X} (h : IsWPDAt g (f x)) : IsWPDAt g x := by
  intro ε hε
  obtain ⟨M, hM⟩ := h (ε + C) (by linarith)
  refine ⟨M, Set.Finite.subset hM ?_⟩
  have hsub := pairStab_subset_map (G := G) (ε := ε) hf hequiv x ((g ^ M) • x)
  rw [hequiv (g ^ M) x] at hsub
  exact hsub

/-- **And pushes forward**, at the same cost. -/
theorem isWPDAt_map {C : ℝ} (hC : 0 ≤ C) {f : X → Y}
    (hf : HasAdditiveDistortion C f) (hequiv : IsEquivariant G f) {g : G}
    {x : X} (h : IsWPDAt g x) : IsWPDAt g (f x) := by
  intro ε hε
  obtain ⟨M, hM⟩ := h (ε + C) (by linarith)
  refine ⟨M, Set.Finite.subset hM ?_⟩
  have hsub := pairStab_map_subset (G := G) (ε := ε) hf hequiv x ((g ^ M) • x)
  rw [hequiv (g ^ M) x] at hsub
  exact hsub

/-- **The whole `AH3Data` payload, transferred at once**, as the three
conclusions rather than as the bundled structure: bundling is left to the
module that owns `AH3Data`, because its `Space` field carries its own universe
and the packaging is where the universe has to be chosen.

Given an equivariant map `f : X → Y` of additive distortion `C`, a target that
is `δ`-hyperbolic with `g` loxodromic and WPD at `f x`, the source is
`(δ + 3C)`-hyperbolic with `g` loxodromic and WPD at `x`. -/
theorem hyperbolic_loxodromic_wpd_of_map {C δ : ℝ} (hC : 0 ≤ C) {f : X → Y}
    (hf : HasAdditiveDistortion C f) (hequiv : IsEquivariant G f) {g : G}
    {x : X} (hY : IsHyperbolicSpace δ Y) (hlox : IsLoxodromic g (f x))
    (hwpd : IsWPDAt g (f x)) :
    IsHyperbolicSpace (δ + 3 * C) X ∧ IsLoxodromic g x ∧ IsWPDAt g x :=
  ⟨isHyperbolicSpace_of_additiveDistortion hf hY,
    isLoxodromic_of_map hC hf hequiv hlox, isWPDAt_of_map hC hf hequiv hwpd⟩

end Transfer

end GGT
end GroupApproximation
