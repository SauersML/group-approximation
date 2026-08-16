import Mathlib.GroupTheory.Coset.Defs
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic

/-!
# Amenable groups

Mathlib has no notion of amenability at all, which is why several
manuscript sentences that use only *elementary* amenability facts have to
cite the literature for the whole sentence rather than for the one deep
theorem they actually depend on.  This file supplies the definition and
the permanence properties that need no analysis, so that those sentences
can be narrowed to their genuine external input.

Amenability is taken here in the finitely-additive-measure form: a
left-invariant finitely additive probability measure defined on *all*
subsets.  That is equivalent to the invariant-mean formulation and is far
easier to manipulate without any functional analysis, which is the point
--- everything below is elementary set theory and group theory.

What is proved: finite groups are amenable, and amenability passes to
subgroups.  The subgroup argument is the classical one, transported to
sets: a right transversal splits the ambient group over the subgroup, the
induced retraction is equivariant for left multiplication by subgroup
elements, and pulling the ambient measure back along it gives an invariant
measure on the subgroup.

What is deliberately NOT here: closure under extensions and under directed
unions.  Both need a limit of measures, hence compactness, hence real
analysis; they are the next layer, not this one.
-/

namespace GroupApproximation
namespace Amenability

/-- A left-invariant finitely additive probability measure on all subsets
of a group.  Left translation is written as an image rather than a scalar
action to keep the statement free of `SMul` instance choices. -/
structure InvariantMean (G : Type*) [Group G] where
  /-- The measure of a subset. -/
  measure : Set G → ℝ
  nonneg : ∀ A, 0 ≤ measure A
  measure_univ : measure Set.univ = 1
  additive : ∀ A B : Set G, Disjoint A B →
    measure (A ∪ B) = measure A + measure B
  invariant : ∀ (g : G) (A : Set G),
    measure ((fun x ↦ g * x) '' A) = measure A

/-- A group is amenable when it carries a left-invariant finitely additive
probability measure on all of its subsets. -/
def IsAmenable (G : Type*) [Group G] : Prop := Nonempty (InvariantMean G)

/-! ## Finite groups -/

/-- Counting measure, normalized, is invariant. -/
noncomputable def finiteMean (G : Type*) [Group G] [Finite G] :
    InvariantMean G where
  measure A := (A.ncard : ℝ) / (Nat.card G : ℝ)
  nonneg A := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  measure_univ := by
    have hpos : (0 : ℝ) < (Nat.card G : ℝ) := by
      have : 0 < Nat.card G := Nat.card_pos
      exact_mod_cast this
    rw [Set.ncard_univ, div_self hpos.ne']
  additive A B hAB := by
    rw [Set.ncard_union_eq hAB A.toFinite B.toFinite]
    push_cast
    rw [add_div]
  invariant g A := by
    rw [Set.ncard_image_of_injective A (mul_right_injective g)]

theorem isAmenable_of_finite (G : Type*) [Group G] [Finite G] :
    IsAmenable G := ⟨finiteMean G⟩

/-! ## Subgroups -/

variable {G : Type*} [Group G] (H : Subgroup G)

/-- A chosen representative of the right coset `H g`. -/
noncomputable def cosetRep (g : G) : G :=
  (Quotient.mk (QuotientGroup.rightRel H) g).out

theorem cosetRep_spec (g : G) : g * (cosetRep H g)⁻¹ ∈ H := by
  have h : Quotient.mk (QuotientGroup.rightRel H) (cosetRep H g) =
      Quotient.mk (QuotientGroup.rightRel H) g := Quotient.out_eq _
  have h2 : QuotientGroup.rightRel H (cosetRep H g) g := Quotient.exact h
  exact QuotientGroup.rightRel_apply.mp h2

theorem cosetRep_mul_left (k : H) (g : G) :
    cosetRep H ((k : G) * g) = cosetRep H g := by
  refine congrArg Quotient.out (Quotient.sound ?_)
  show QuotientGroup.rightRel H ((k : G) * g) g
  refine QuotientGroup.rightRel_apply.mpr ?_
  have hg : g * ((k : G) * g)⁻¹ = (k : G)⁻¹ := by
    rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [hg]
  exact H.inv_mem k.2

/-- The retraction of the ambient group onto the subgroup determined by the
chosen right transversal. -/
noncomputable def retract (g : G) : H := ⟨g * (cosetRep H g)⁻¹, cosetRep_spec H g⟩

theorem retract_mul_left (k : H) (g : G) :
    retract H ((k : G) * g) = k * retract H g := by
  refine Subtype.ext ?_
  show (k : G) * g * (cosetRep H ((k : G) * g))⁻¹ =
    (k : G) * (g * (cosetRep H g)⁻¹)
  rw [cosetRep_mul_left, mul_assoc]

theorem preimage_image_retract (k : H) (A : Set H) :
    retract H ⁻¹' ((fun x ↦ k * x) '' A) =
      (fun x : G ↦ (k : G) * x) '' (retract H ⁻¹' A) := by
  ext g
  constructor
  · rintro ⟨a, ha, hka⟩
    refine ⟨(k : G)⁻¹ * g, ?_, ?_⟩
    swap
    · show (k : G) * ((k : G)⁻¹ * g) = g
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    have hret : retract H ((k : G)⁻¹ * g) = k⁻¹ * retract H g := by
      have := retract_mul_left H k⁻¹ g
      simpa using this
    rw [Set.mem_preimage, hret, ← hka]
    simpa using ha
  · rintro ⟨x, hx, rfl⟩
    refine ⟨retract H x, hx, ?_⟩
    rw [retract_mul_left]

/-- Pulling an invariant measure back along the retraction gives an
invariant measure on the subgroup. -/
noncomputable def subgroupMean (m : InvariantMean G) : InvariantMean H where
  measure A := m.measure (retract H ⁻¹' A)
  nonneg _ := m.nonneg _
  measure_univ := by
    have h : retract H ⁻¹' (Set.univ : Set H) = Set.univ := by simp
    rw [h, m.measure_univ]
  additive A B hAB := by
    rw [Set.preimage_union]
    exact m.additive _ _ (hAB.preimage _)
  invariant k A := by
    rw [preimage_image_retract, m.invariant]

/-- **Amenability passes to subgroups.** -/
theorem IsAmenable.subgroup (h : IsAmenable G) (H : Subgroup G) :
    IsAmenable H := by
  obtain ⟨m⟩ := h
  exact ⟨subgroupMean H m⟩

end Amenability
end GroupApproximation
