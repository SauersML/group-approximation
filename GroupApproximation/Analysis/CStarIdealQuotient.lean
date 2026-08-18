import GroupApproximation.Analysis.CStarQuotientHom
import Mathlib.Analysis.Normed.Group.Quotient

/-!
# The quotient of a noncommutative normed ⋆-ring by a two-sided ideal

## The gap this closes

The standing record in `CStarExactness.lean` itemises what blocks a
noncommutative C⋆-quotient, and its first item is elementary but real:
Mathlib's `Ideal.Quotient.semiNormedCommRing` and `normedCommRing`
(`Analysis/Normed/Group/Quotient.lean`) are **commutative only**, so even the
seminormed quotient *ring* must be redone noncommutatively before the
C⋆-identity on the quotient can be approached.  This module redoes it.

For a two-sided ideal `I` of a seminormed ring `R`:

* `quotientSeminormedRing` -- the quotient norm is submultiplicative, by the
  same `ε`-of-room argument Mathlib's commutative instance uses, which never
  needed commutativity;
* `quotientNormedRing` -- a norm when `I` is closed;
* `quotientNormedAlgebra` -- the scalars descend;
* `quotientNormedStarGroup` -- for a star-stable ideal the involution is
  isometric on the quotient, because `star` permutes the coset of `x` into
  the coset of `star x` norm-preservingly.

Completeness of the quotient of a complete ring is already
comm-agnostic in Mathlib (`Submodule.Quotient.completeSpace`), and the
⋆-ring structure of the quotient by a star-stable two-sided ideal is
`CStarSeminormQuotient.quotientStarRing`.  With this module the quotient of
a C⋆-algebra by a closed star-stable two-sided ideal is a complete normed
⋆-algebra.

## What is deliberately not here

The **C⋆-identity** for the quotient norm.  That is the second half of the
standing record's quotient item, its proof runs through an approximate unit
of the ideal, and it belongs to a separate module so that this one stays a
pure mirror of Mathlib's commutative instances.  Until it lands, `B ⧸ J` is
a complete normed ⋆-algebra and **not yet** certified a C⋆-algebra, and no
declaration here claims otherwise.

## Manuscript status

Infrastructure; certifies no manuscript step on its own.  `SO.16` and
`RE.05` remain **MISSING**.
-/

namespace GroupApproximation
namespace CStarTensor

open Metric

universe u

section Seminormed

variable {R : Type u} [SeminormedRing R] (I : Ideal R) [I.IsTwoSided]

/-- Coset representatives approximate the quotient norm: the noncommutative
mirror of `Ideal.Quotient.norm_mk_lt`, delegated to the comm-agnostic
`Submodule.Quotient.norm_mk_lt`. -/
theorem quotient_norm_mk_lt (x : R ⧸ I) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : R, Ideal.Quotient.mk I r = x ∧ ‖r‖ < ‖x‖ + ε :=
  Submodule.Quotient.norm_mk_lt x hε

/-- The quotient map does not increase norms. -/
theorem quotient_norm_mk_le (r : R) : ‖Ideal.Quotient.mk I r‖ ≤ ‖r‖ :=
  Submodule.Quotient.norm_mk_le r

/-- **The quotient of a seminormed ring by a two-sided ideal is a seminormed
ring.**  The submultiplicativity proof is Mathlib's commutative one verbatim
-- pick representatives within `ε₁, ε₂` of the quotient norms and let
continuity of multiplication close the gap -- because that argument never
multiplies two cosets in a way that needs commutativity.

Priority `100`: on a commutative ring Mathlib's
`Ideal.Quotient.semiNormedCommRing` supplies the same data through the same
group-quotient norm, so the diamond is harmless, but Mathlib's instance
should win where it applies. -/
noncomputable instance (priority := 100) quotientSeminormedRing :
    SeminormedRing (R ⧸ I) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le x y := le_of_forall_pos_le_add fun ε hε => by
    have := ((nhds_basis_ball.prod_nhds nhds_basis_ball).tendsto_iff
      nhds_basis_ball).mp (continuous_mul.tendsto (‖x‖, ‖y‖)) ε hε
    simp only [Set.mem_prod, mem_ball, and_imp, Prod.forall,
      Prod.exists] at this
    rcases this with ⟨ε₁, ε₂, ⟨h₁, h₂⟩, h⟩
    obtain ⟨⟨a, rfl, ha⟩, ⟨b, rfl, hb⟩⟩ := quotient_norm_mk_lt I x h₁,
      quotient_norm_mk_lt I y h₂
    simp only [dist, abs_sub_lt_iff] at h
    specialize h ‖a‖ ‖b‖ ⟨by linarith, by linarith [quotient_norm_mk_le I a]⟩
      ⟨by linarith, by linarith [quotient_norm_mk_le I b]⟩
    calc
      _ ≤ ‖a‖ * ‖b‖ :=
        (quotient_norm_mk_le I (a * b)).trans (norm_mul_le a b)
      _ ≤ _ := (sub_lt_iff_lt_add'.mp h.1).le

/-- **The involution is isometric on the quotient by a star-stable two-sided
ideal**: `star` carries the coset of `x` onto the coset of `star x`
norm-preservingly, so the two infima agree. -/
noncomputable instance (priority := 100) quotientNormedStarGroup
    [StarRing R] [NormedStarGroup R] [IsStarStable I] :
    NormedStarGroup (R ⧸ I) where
  norm_star_le x := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨r, rfl, hr⟩ := quotient_norm_mk_lt I x hε
    calc ‖star (Ideal.Quotient.mk I r)‖
        = ‖Ideal.Quotient.mk I (star r)‖ := by rw [quotient_star_mk]
      _ ≤ ‖star r‖ := quotient_norm_mk_le I (star r)
      _ = ‖r‖ := norm_star r
      _ ≤ ‖Ideal.Quotient.mk I r‖ + ε := hr.le

end Seminormed

section Normed

variable {R : Type u} [NormedRing R] {I : Ideal R} [I.IsTwoSided]

/-- The quotient of a normed ring by a **closed** two-sided ideal is a
normed ring: the group-quotient norm is definite on the quotient by a closed
subgroup. -/
noncomputable instance (priority := 100) quotientNormedRing
    [IsClosed (I : Set R)] : NormedRing (R ⧸ I) :=
  { quotientSeminormedRing I, Submodule.Quotient.normedAddCommGroup I with }

end Normed

section Algebra

variable (𝕜 : Type*) [NormedField 𝕜] {R : Type u} [SeminormedRing R]
  [NormedAlgebra 𝕜 R] (I : Ideal R) [I.IsTwoSided]

/-- The scalars descend to the quotient: the noncommutative mirror of
`Ideal.Quotient.normedAlgebra`. -/
noncomputable instance (priority := 100) quotientNormedAlgebra :
    NormedAlgebra 𝕜 (R ⧸ I) :=
  { Submodule.Quotient.normedSpace I 𝕜, Ideal.Quotient.algebra 𝕜 with }

end Algebra

end CStarTensor
end GroupApproximation
