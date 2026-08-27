import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The quotient of a C-star algebra by a closed, star-closed two-sided ideal

Mathlib quotients normed *groups* by closed subgroups and stops there: there is
no normed-ring quotient by a closed two-sided ideal, and no `CStarRing`
instance on any quotient.  `Analysis/NormMatrixCorona` therefore builds the
matrix corona's ring, norm and star structure by hand.  Reading that
construction, every step of it except the C-star identity is generic in the
pair (ambient C-star algebra, closed star-closed two-sided ideal) — it uses
only `Submodule.Quotient.norm_mk_lt`, `Submodule.Quotient.norm_mk_le`,
submultiplicativity in the ambient, and `QuotientAddGroup.lift`.

This module is that construction, written once.  The matrix corona and the
Calkin algebra are both instances of it; the corona's own copy is left alone,
since refactoring a wired module is not something to do without a compiler.

## Why these are `def`s and not `instance`s

`FilterMatrixCoronaAlgebra X l` *is* `BoundedMatrixSequence X ⧸ nullMatrixSequenceIdeal X l`,
so global instances on `A ⧸ I` would collide with the corona's hand-built ones
on the same type.  Everything below is therefore a `def`, to be installed on an
opaque type synonym by the consumer — the pattern
`Analysis/NormMatrixCorona` already uses for `NormMatrixCStarCorona`.

## What is not here

The C-star identity.  It is now *stateable*, because the norm and the star are
built below, and it is `CStarIdentityStatement`.  Its standard proof runs
through an approximate unit of the ideal, and it does not follow from the
corona's argument: that one is a `limsup` computation available only because
that quotient is an `ℓ^∞` product modulo a null ideal.

This module is not in the root import list.  It was authored while builds were
suspended, so it is kept out of the closure until it has been elaborated.
-/

namespace GroupApproximation
namespace CStarQuotient

noncomputable section

/-- A two-sided ideal closed under the involution.  Carried as a class so that
the star on the quotient can be built without a loose hypothesis. -/
class IsStarIdeal {A : Type} [CStarAlgebra A] (I : Ideal A) : Prop where
  star_mem : ∀ {a : A}, a ∈ I → star a ∈ I

variable (A : Type) [CStarAlgebra A] (I : Ideal A) [I.IsTwoSided]
  [hIclosed : IsClosed (I : Set A)]

/-! ## Representatives of prescribed norm -/

theorem exists_rep_norm_lt (x : A ⧸ I) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, Ideal.Quotient.mk I a = x ∧ ‖a‖ < ‖x‖ + ε :=
  Submodule.Quotient.norm_mk_lt x hε

theorem norm_mk_le (a : A) : ‖Ideal.Quotient.mk I a‖ ≤ ‖a‖ :=
  Submodule.Quotient.norm_mk_le I a

private theorem real_mul_continuousAt (x y : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ ↦ p.1 * p.2) (x, y) :=
  (continuous_fst.mul continuous_snd).continuousAt

/-! ## Ring, norm and completeness -/

/-- The quotient seminorm is submultiplicative.  Transplanted verbatim from
`filterMatrixCoronaAlgebraSeminormedRing`; nothing in the argument mentions
sequences. -/
def seminormedRing : SeminormedRing (A ⧸ I) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le x y := _root_.le_of_forall_pos_le_add fun ε hε ↦ by
    obtain ⟨δ, hδ, hbound⟩ :=
      Metric.continuousAt_iff.mp (real_mul_continuousAt ‖x‖ ‖y‖) ε hε
    have hδ3 : 0 < δ / 3 := div_pos hδ (by norm_num)
    obtain ⟨a, ha_eq, ha⟩ := exists_rep_norm_lt A I x hδ3
    obtain ⟨b, hb_eq, hb⟩ := exists_rep_norm_lt A I y hδ3
    rw [← ha_eq, ← hb_eq]
    have hpair : dist (‖a‖, ‖b‖)
          (‖Ideal.Quotient.mk I a‖, ‖Ideal.Quotient.mk I b‖) < δ := by
      rw [Prod.dist_eq]
      simp only [Real.dist_eq]
      rw [max_lt_iff]
      constructor
      · rw [abs_of_nonneg]
        · rw [← ha_eq] at ha
          linarith
        · exact sub_nonneg.mpr (norm_mk_le A I a)
      · rw [abs_of_nonneg]
        · rw [← hb_eq] at hb
          linarith
        · exact sub_nonneg.mpr (norm_mk_le A I b)
    have hpair' : dist (‖a‖, ‖b‖) (‖x‖, ‖y‖) < δ := by
      simpa only [ha_eq, hb_eq] using hpair
    have hprod := hbound hpair'
    simp only [Real.dist_eq] at hprod
    have hupper : ‖a‖ * ‖b‖ < ‖x‖ * ‖y‖ + ε :=
      sub_lt_iff_lt_add'.mp (abs_lt.mp hprod).2
    calc
      ‖Ideal.Quotient.mk I (a * b)‖ ≤ ‖a * b‖ := norm_mk_le A I (a * b)
      _ ≤ ‖a‖ * ‖b‖ := norm_mul_le a b
      _ ≤ ‖Ideal.Quotient.mk I a‖ * ‖Ideal.Quotient.mk I b‖ + ε := by
          simpa only [ha_eq, hb_eq] using hupper.le

/-- Because the ideal is closed, the quotient seminorm is a norm. -/
def normedRing : NormedRing (A ⧸ I) :=
  { seminormedRing A I, Submodule.Quotient.normedAddCommGroup I with }

/-- The quotient of a complete space by a closed submodule is complete. -/
def completeSpace : CompleteSpace (A ⧸ I) :=
  Submodule.Quotient.completeSpace I

/-! ## The descended involution -/

variable [IsStarIdeal I]

private def starHom : A →+ A ⧸ I :=
  (Ideal.Quotient.mk I).toAddMonoidHom.comp starAddEquiv.toAddMonoidHom

private theorem le_star_ker : I.toAddSubgroup ≤ (starHom A I).ker := by
  intro a ha
  change Ideal.Quotient.mk I (star a) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact IsStarIdeal.star_mem ha

/-- The involution descends to the quotient. -/
def starInstance : Star (A ⧸ I) where
  star := QuotientAddGroup.lift I.toAddSubgroup (starHom A I) (le_star_ker A I)

@[simp] theorem star_mk (a : A) :
    letI := starInstance A I
    star (Ideal.Quotient.mk I a) = Ideal.Quotient.mk I (star a) :=
  QuotientAddGroup.lift_mk _ _ _

/-- The descended involution is involutive. -/
def involutiveStar : InvolutiveStar (A ⧸ I) :=
  letI := starInstance A I
  { star := star
    star_involutive := fun x ↦ by
      induction x using QuotientAddGroup.induction_on with
      | _ a =>
        change star (star (Ideal.Quotient.mk I a)) = Ideal.Quotient.mk I a
        rw [star_mk, star_mk, star_star] }

/-- The descended involution is a ring involution. -/
def starRing : StarRing (A ⧸ I) :=
  letI := seminormedRing A I
  letI := involutiveStar A I
  { star_add := fun x y ↦ by
      induction x using QuotientAddGroup.induction_on with
      | _ a =>
        induction y using QuotientAddGroup.induction_on with
        | _ b =>
          change star (Ideal.Quotient.mk I (a + b)) =
            star (Ideal.Quotient.mk I a) + star (Ideal.Quotient.mk I b)
          rw [star_mk, star_mk, star_mk, star_add]
          rfl
    star_mul := fun x y ↦ by
      induction x using QuotientAddGroup.induction_on with
      | _ a =>
        induction y using QuotientAddGroup.induction_on with
        | _ b =>
          change star (Ideal.Quotient.mk I (a * b)) =
            star (Ideal.Quotient.mk I b) * star (Ideal.Quotient.mk I a)
          rw [star_mk, star_mk, star_mk,
            show star (a * b) = star b * star a from StarMul.star_mul a b]
          rfl }

/-- The descended involution is norm-contractive, hence isometric. -/
def normedStarGroup : letI := normedRing A I; letI := starRing A I;
    NormedStarGroup (A ⧸ I) :=
  letI := normedRing A I
  letI := starRing A I
  { norm_star_le := fun x ↦ by
      apply _root_.le_of_forall_pos_le_add
      intro ε hε
      obtain ⟨a, rfl, ha⟩ := exists_rep_norm_lt A I x hε
      rw [star_mk]
      exact ((norm_mk_le A I (star a)).trans_lt (by simpa using ha)).le }

/-! ## The complex structure -/

/-- The quotient's complex algebra structure is compatible with the quotient
norm. -/
def normedAlgebra : letI := normedRing A I; NormedAlgebra ℂ (A ⧸ I) :=
  letI := normedRing A I
  ⟨fun z x ↦ (norm_smul z x).le⟩

/-- The descended involution is conjugate-linear. -/
def starModule : letI := starInstance A I; StarModule ℂ (A ⧸ I) :=
  letI := starInstance A I
  { star_smul := fun z x ↦ by
      induction x using QuotientAddGroup.induction_on with
      | _ a =>
        change star (Ideal.Quotient.mk I (z • a)) =
          star z • star (Ideal.Quotient.mk I a)
        rw [star_mk, star_mk, star_smul]
        rfl }

/-! ## The one residual -/

/-- **The C-star identity for the quotient norm.**  Everything above is
unconditional; this is the single statement the construction still owes, and
with the norm and the star built it can finally be written down.

Its standard proof takes an approximate unit `(u_λ)` of `I` and computes
`‖a + I‖ = lim ‖a(1 - u_λ)‖`, from which the identity follows by the C-star
identity in `A`.  Mathlib has no quotient C-star instance of any kind, so this
is a genuine piece of C-star theory the repository would need — and would be
worth having independently of the Calkin algebra it is wanted for. -/
def CStarIdentityStatement : Prop :=
  ∀ (A : Type) [CStarAlgebra A] (I : Ideal A) [I.IsTwoSided]
    [IsClosed (I : Set A)] [IsStarIdeal I],
    letI := normedRing A I
    letI := starRing A I
    ∀ x : A ⧸ I, ‖x‖ * ‖x‖ ≤ ‖star x * x‖

end

end CStarQuotient
end GroupApproximation
