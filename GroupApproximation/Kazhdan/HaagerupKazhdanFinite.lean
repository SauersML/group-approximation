import GroupApproximation.Kazhdan.DelormeFixedPoint
import GroupApproximation.Meta.AxiomGuard

/-!
# The Haagerup property, and why a Kazhdan group with it is finite

`non_mf_groups_exist.tex`, the remark after `prop:torsion-defect-ring`
(tex lines 1146--1150):

> Every countable subgroup of `GL_2` over a field has the Haagerup property,
> and the kernel of `GL_2(J) → GL_2(F_2[z,z^{-1}])` is locally finite, so a
> Kazhdan subgroup of `GL_2(J)` has finite image in `GL_2(F_2(z))` …

The Haagerup property (Gromov's a-T-menability) of a discrete group `G` is the
existence of a metrically proper affine isometric action on a real Hilbert
space: an orthogonal representation `π` and a cocycle `b` for it such that
every ball `{g : ‖b g‖ ≤ R}` is finite.  This module fixes that definition,
proves that it passes to subgroups, and proves the step the printed sentence
consumes: a group with property `(T)` and the Haagerup property is finite.

The proof is Delorme's theorem, proved in `Kazhdan/DelormeFixedPoint` rather
than cited: the affine action `x ↦ π g x + b g` has a fixed point `x`, so
`b g = x - π g x` and `‖b g‖ ≤ 2‖x‖` for every `g`; properness makes the whole
group one finite ball.
-/

namespace GroupApproximation
namespace Haagerup

universe u v w

open Delorme

/-- A metrically proper affine isometric action of a discrete group on a
complete real inner product space, at Hilbert-space universe `v`: an orthogonal
representation `π`, a cocycle `b` for it, and finiteness of every ball
`{g : ‖b g‖ ≤ R}`. -/
structure ProperAffineAction (G : Type u) [Group G] where
  /-- The Hilbert space acted on. -/
  E : Type v
  [normed : NormedAddCommGroup E]
  [inner : InnerProductSpace ℝ E]
  [complete : CompleteSpace E]
  /-- The linear part of the action. -/
  π : G →* (E ≃ₗᵢ[ℝ] E)
  /-- The translation part of the action. -/
  b : G → E
  isCocycle : IsCocycle π b
  proper : ∀ R : ℝ, {g : G | ‖b g‖ ≤ R}.Finite

attribute [instance] ProperAffineAction.normed ProperAffineAction.inner
  ProperAffineAction.complete

/-- **The Haagerup property** of a discrete group: it admits a metrically
proper affine isometric action on a real Hilbert space (in `Type v`). -/
def HasHaagerupProperty (G : Type u) [Group G] : Prop :=
  Nonempty (ProperAffineAction.{u, v} G)

namespace ProperAffineAction

variable {G : Type u} [Group G]

/-- A proper affine action pulls back along an injective homomorphism. -/
def comap {H : Type w} [Group H] (A : ProperAffineAction.{u, v} G) (ι : H →* G)
    (hι : Function.Injective ι) : ProperAffineAction.{w, v} H where
  E := A.E
  π := A.π.comp ι
  b := fun h ↦ A.b (ι h)
  isCocycle := fun g h ↦ by
    simpa [MonoidHom.comp_apply] using A.isCocycle (ι g) (ι h)
  proper := fun R ↦
    Set.Finite.preimage (f := ι) (s := {g : G | ‖A.b g‖ ≤ R})
      (fun _ _ _ _ h ↦ hι h) (A.proper R)

/-- **Delorme consumption.**  A group with property `(T)` that acts properly
by affine isometries on a real Hilbert space is finite. -/
theorem finite_of_hasKazhdanPropertyT (A : ProperAffineAction.{u, v} G)
    (hT : HasKazhdanPropertyT.{u, u} G) : Finite G := by
  obtain ⟨x, hx⟩ := exists_fixed_point_of_hasKazhdanPropertyT hT A.π A.isCocycle
  have hbound : ∀ g : G, ‖A.b g‖ ≤ 2 * ‖x‖ := by
    intro g
    have hbg : A.b g = x - A.π g x := by
      rw [eq_sub_iff_add_eq, add_comm]
      exact hx g
    rw [hbg]
    calc ‖x - A.π g x‖ ≤ ‖x‖ + ‖A.π g x‖ := norm_sub_le _ _
      _ = 2 * ‖x‖ := by rw [LinearIsometryEquiv.norm_map]; ring
  have hfin : (Set.univ : Set G).Finite :=
    (A.proper (2 * ‖x‖)).subset fun g _ ↦ hbound g
  exact Set.finite_univ_iff.mp hfin

end ProperAffineAction

/-- The Haagerup property passes to groups that embed. -/
theorem HasHaagerupProperty.comap {G : Type u} [Group G] {H : Type w} [Group H]
    (hG : HasHaagerupProperty.{u, v} G) (ι : H →* G) (hι : Function.Injective ι) :
    HasHaagerupProperty.{w, v} H :=
  Nonempty.map (fun A ↦ A.comap ι hι) hG

/-- The Haagerup property passes to subgroups. -/
theorem HasHaagerupProperty.subgroup {G : Type u} [Group G]
    (hG : HasHaagerupProperty.{u, v} G) (H : Subgroup G) :
    HasHaagerupProperty.{u, v} H :=
  hG.comap H.subtype H.subtype_injective

/-- **A group with property `(T)` and the Haagerup property is finite.** -/
theorem finite_of_hasKazhdanPropertyT_of_hasHaagerupProperty {G : Type u} [Group G]
    (hT : HasKazhdanPropertyT.{u, u} G) (hH : HasHaagerupProperty.{u, v} G) :
    Finite G := by
  obtain ⟨A⟩ := hH
  exact A.finite_of_hasKazhdanPropertyT hT

/-- The consumption step as a closed proposition: in every universe pair, a
discrete group with property `(T)` and the Haagerup property is finite. -/
theorem kazhdanHaagerupFinite :
    ∀ (G : Type u) [Group G], HasKazhdanPropertyT.{u, u} G →
      HasHaagerupProperty.{u, v} G → Finite G :=
  fun _ _ hT hH ↦ finite_of_hasKazhdanPropertyT_of_hasHaagerupProperty hT hH

end Haagerup
end GroupApproximation

#audit_axioms GroupApproximation.Haagerup.ProperAffineAction.finite_of_hasKazhdanPropertyT
#audit_axioms GroupApproximation.Haagerup.HasHaagerupProperty.subgroup
#audit_closed_axioms GroupApproximation.Haagerup.kazhdanHaagerupFinite
