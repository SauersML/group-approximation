import GroupApproximation.Higman.HNNCentralizer
import Mathlib.GroupTheory.Coprod.Basic

/-!
# The amalgamated free product as a presented quotient, and its finiteness

Higman's constructions glue two finitely presented groups along a common
finitely generated subgroup, and the resulting group has to be finitely
presented again.  Mathlib has the amalgamated product as `Monoid.PushoutI`,
with its normal form theorem, but nothing about finite presentation; the
repository has `HNNFinitePresentation` for the HNN half and nothing for this
one.  This file is the missing half.

The construction is the classical presentation: the free product `K₁ ∗ K₂`
modulo the relators `e₁(g) · e₂(g)⁻¹`, one for each `g` in a generating set
of the amalgamated group `G`.  Two things have to be checked, and both are
short:

* **A generating set suffices.**  The set of `g` at which the two composite
  homomorphisms `G → K₁ ∗ K₂ → Q` agree is the equalizer of two
  homomorphisms, hence a subgroup; if it contains a generating set it is
  everything.  This is the same argument `ProductFinitePresentation` uses for
  the commutators, and it is why the relator set may be taken finite.
* **Finite presentation.**  `K₁ ∗ K₂` is finitely presented when both factors
  are (Mathlib), and a quotient by the normal closure of a finite set of a
  finitely presented group is finitely presented (Mathlib), so the amalgam
  is.

What this file does *not* do is identify the quotient with `PushoutI`; that
identification, which is what carries the normal form theorem across, is
`Higman.AmalgamNormalForm`.  The two are kept apart because only the finite
presentation is needed to *build* Higman's overgroups, while only the normal
form is needed to *compute* the intersections inside them.
-/

namespace GroupApproximation
namespace Higman
namespace Amalgam

open scoped Monoid.Coprod

variable {G K₁ K₂ : Type} [Group G] [Group K₁] [Group K₂]
  (e₁ : G →* K₁) (e₂ : G →* K₂)

/-! ## 1.  The relators -/

/-- The relator attached to one element of the amalgamated group. -/
def relator (g : G) : K₁ ∗ K₂ :=
  Monoid.Coprod.inl (e₁ g) * (Monoid.Coprod.inr (e₂ g))⁻¹

/-- The relators attached to a set of elements. -/
def relators (S : Set G) : Set (K₁ ∗ K₂) := relator e₁ e₂ '' S

theorem relators_finite {S : Set G} (hS : S.Finite) :
    (relators e₁ e₂ S).Finite :=
  hS.image _

/-- The normal subgroup by which the free product is divided. -/
def Rel (S : Set G) : Subgroup (K₁ ∗ K₂) :=
  Subgroup.normalClosure (relators e₁ e₂ S)

instance Rel_normal (S : Set G) : (Rel e₁ e₂ S).Normal := by
  unfold Rel
  infer_instance

/-- **The amalgamated free product**, as a presented quotient of the free
product.  The relators are taken over all of `G`; `Rel_eq_of_closure` says a
generating set gives the same subgroup, which is what makes the presentation
finite. -/
abbrev Amalg : Type := (K₁ ∗ K₂) ⧸ Rel e₁ e₂ Set.univ

/-- The left injection. -/
def inl : K₁ →* Amalg e₁ e₂ :=
  (QuotientGroup.mk' (Rel e₁ e₂ Set.univ)).comp Monoid.Coprod.inl

/-- The right injection. -/
def inr : K₂ →* Amalg e₁ e₂ :=
  (QuotientGroup.mk' (Rel e₁ e₂ Set.univ)).comp Monoid.Coprod.inr

/-- The amalgamation: the two copies of `G` are identified. -/
theorem inl_comp_eq_inr_comp : (inl e₁ e₂).comp e₁ = (inr e₁ e₂).comp e₂ := by
  refine MonoidHom.ext fun g => ?_
  have hmem : relator e₁ e₂ g ∈ Rel e₁ e₂ Set.univ :=
    Subgroup.subset_normalClosure ⟨g, Set.mem_univ g, rfl⟩
  have h1 : (QuotientGroup.mk' (Rel e₁ e₂ Set.univ)) (relator e₁ e₂ g) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hmem
  have h2 : (QuotientGroup.mk' (Rel e₁ e₂ Set.univ))
        (Monoid.Coprod.inl (e₁ g)) *
      ((QuotientGroup.mk' (Rel e₁ e₂ Set.univ))
        (Monoid.Coprod.inr (e₂ g)))⁻¹ = 1 := by
    rw [← map_inv, ← map_mul]
    exact h1
  have := mul_inv_eq_one.mp h2
  exact this

/-! ## 2.  A generating set suffices -/

/-- **The relators over a generating set already give the whole relation
subgroup.**  The elements at which the two composites agree form the
equalizer of two homomorphisms `G → (K₁ ∗ K₂) ⧸ Rel S`, hence a subgroup; it
contains `S`, so it is everything. -/
theorem Rel_eq_of_closure {S : Set G} (hS : Subgroup.closure S = ⊤) :
    Rel e₁ e₂ S = Rel e₁ e₂ Set.univ := by
  refine le_antisymm ?_ ?_
  · refine Subgroup.normalClosure_mono ?_
    rintro _ ⟨g, -, rfl⟩
    exact ⟨g, Set.mem_univ g, rfl⟩
  · refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨g, -, rfl⟩
    set π := QuotientGroup.mk' (Rel e₁ e₂ S) with hπ
    set ψ₁ : G →* (K₁ ∗ K₂) ⧸ Rel e₁ e₂ S :=
      (π.comp Monoid.Coprod.inl).comp e₁ with hψ₁
    set ψ₂ : G →* (K₁ ∗ K₂) ⧸ Rel e₁ e₂ S :=
      (π.comp Monoid.Coprod.inr).comp e₂ with hψ₂
    have hsub : S ⊆ (ψ₁.eqLocus ψ₂ : Set G) := by
      intro s hs
      have hmem : relator e₁ e₂ s ∈ Rel e₁ e₂ S :=
        Subgroup.subset_normalClosure ⟨s, hs, rfl⟩
      have h1 : π (relator e₁ e₂ s) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hmem
      have h2 : π (Monoid.Coprod.inl (e₁ s)) *
          (π (Monoid.Coprod.inr (e₂ s)))⁻¹ = 1 := by
        rw [← map_inv, ← map_mul]
        exact h1
      have := mul_inv_eq_one.mp h2
      exact this
    have htop : ψ₁.eqLocus ψ₂ = ⊤ := by
      refine top_le_iff.mp ?_
      rw [← hS]
      exact Subgroup.closure_le _ |>.mpr hsub
    have hg : g ∈ ψ₁.eqLocus ψ₂ := by
      rw [htop]
      exact Subgroup.mem_top g
    have hgg : ψ₁ g = ψ₂ g := hg
    have hval : π (Monoid.Coprod.inl (e₁ g)) = π (Monoid.Coprod.inr (e₂ g)) := hgg
    have : π (relator e₁ e₂ g) = 1 := by
      unfold relator
      rw [map_mul, map_inv, hval]
      exact mul_inv_cancel _
    exact (QuotientGroup.eq_one_iff _).mp this

/-! ## 3.  Finite presentation -/

/-- **The amalgamated free product of two finitely presented groups along a
finitely generated group is finitely presented.**

Not in Mathlib, and the companion of the repository's
`HNNFinitePresentation.isFinitelyPresented_hnnExtension`. -/
theorem isFinitelyPresented_amalg [Group.IsFinitelyPresented K₁]
    [Group.IsFinitelyPresented K₂] [Group.FG G] :
    Group.IsFinitelyPresented (Amalg e₁ e₂) := by
  obtain ⟨S, hS, hSfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG G)
  refine Group.IsFinitelyPresented.quotient (Rel e₁ e₂ Set.univ) ?_
  refine ⟨relators e₁ e₂ S, relators_finite e₁ e₂ hSfin, ?_⟩
  exact Rel_eq_of_closure e₁ e₂ hS

end Amalgam
end Higman
end GroupApproximation
