import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.Polar.AbsSubalg
import Mathlib.Analysis.CStarAlgebra.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Absolute value, lane `nm-tww-17a`: the ⋆-structure on `adjSub E`

Here `star f` is the adjoint `adjCLM`. Every algebraic identity is checked by uniqueness of
adjoints (`star_apply_eq`). The C⋆-identity is the usual estimate:
`‖f x‖² = ‖⟨x, f⋆ f x⟩‖ ≤ ‖x‖ · ‖f⋆ f‖ · ‖x‖`, so `‖f‖² ≤ ‖f⋆ f‖`.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp

open GroupApproximation.HilbertModule

universe v

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable {E : CStarModule.{v, v} B}

/-- The adjoint, as a star. -/
noncomputable instance instStar : Star (adjSub E) :=
  ⟨fun f => ⟨adjCLM f.2, adjCLM_mem f.2⟩⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.instStar

theorem inner_apply_star (f : adjSub E) (x y : E.carrier) :
    E.inner ((f : E.carrier →L[ℂ] E.carrier) x) y
      = E.inner x (((star f : adjSub E) : E.carrier →L[ℂ] E.carrier) y) :=
  inner_apply_adjCLM f.2 x y

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.inner_apply_star

theorem inner_star_apply (f : adjSub E) (x y : E.carrier) :
    E.inner (((star f : adjSub E) : E.carrier →L[ℂ] E.carrier) x) y
      = E.inner x ((f : E.carrier →L[ℂ] E.carrier) y) :=
  inner_adjCLM_apply f.2 x y

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.inner_star_apply

theorem star_apply_eq (f : adjSub E) (g : E.carrier → E.carrier)
    (hg : ∀ x y : E.carrier, E.inner ((f : E.carrier →L[ℂ] E.carrier) x) y = E.inner x (g y))
    (y : E.carrier) : ((star f : adjSub E) : E.carrier →L[ℂ] E.carrier) y = g y :=
  adjCLM_eq f.2 g hg y

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.star_apply_eq

theorem ext_apply {f g : adjSub E}
    (h : ∀ y : E.carrier, (f : E.carrier →L[ℂ] E.carrier) y = (g : E.carrier →L[ℂ] E.carrier) y) :
    f = g :=
  Subtype.ext (ContinuousLinearMap.ext h)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.ext_apply

/-- `adjSub E` is a ⋆-ring. -/
noncomputable instance instStarRing : StarRing (adjSub E) where
  star_involutive f := ext_apply fun y =>
    star_apply_eq (star f) (fun z => (f : E.carrier →L[ℂ] E.carrier) z)
      (fun x z => inner_star_apply f x z) y
  star_mul f g := ext_apply fun y =>
    star_apply_eq (f * g)
      (fun z => ((star g : adjSub E) : E.carrier →L[ℂ] E.carrier)
        (((star f : adjSub E) : E.carrier →L[ℂ] E.carrier) z))
      (fun x z => by
        change E.inner ((f : E.carrier →L[ℂ] E.carrier) ((g : E.carrier →L[ℂ] E.carrier) x)) z
          = E.inner x (((star g : adjSub E) : E.carrier →L[ℂ] E.carrier)
            (((star f : adjSub E) : E.carrier →L[ℂ] E.carrier) z))
        rw [inner_apply_star f, inner_apply_star g]) y
  star_add f g := ext_apply fun y =>
    star_apply_eq (f + g)
      (fun z => ((star f : adjSub E) : E.carrier →L[ℂ] E.carrier) z
        + ((star g : adjSub E) : E.carrier →L[ℂ] E.carrier) z)
      (fun x z => by
        change E.inner ((f : E.carrier →L[ℂ] E.carrier) x + (g : E.carrier →L[ℂ] E.carrier) x) z
          = E.inner x (((star f : adjSub E) : E.carrier →L[ℂ] E.carrier) z
            + ((star g : adjSub E) : E.carrier →L[ℂ] E.carrier) z)
        rw [E.inner_add_left, E.inner_add_right, inner_apply_star f, inner_apply_star g]) y

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.instStarRing

/-- `adjSub E` is a ⋆-module over `ℂ`. -/
instance instStarModule : StarModule ℂ (adjSub E) where
  star_smul c f := ext_apply fun y =>
    star_apply_eq (c • f)
      (fun z => star c • ((star f : adjSub E) : E.carrier →L[ℂ] E.carrier) z)
      (fun x z => by
        change E.inner (c • (f : E.carrier →L[ℂ] E.carrier) x) z
          = E.inner x (star c • ((star f : adjSub E) : E.carrier →L[ℂ] E.carrier) z)
        rw [E.inner_smul_left, inner_apply_star f, E.inner_smul_right, starRingEnd_apply]) y

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.instStarModule

/-- **The C⋆-identity** on `adjSub E`. -/
instance instCStarRing : CStarRing (adjSub E) where
  norm_mul_self_le f := by
    have hK : 0 ≤ ‖star f * f‖ := norm_nonneg _
    have hb : ∀ x : E.carrier,
        ‖(f : E.carrier →L[ℂ] E.carrier) x‖ ≤ Real.sqrt ‖star f * f‖ * ‖x‖ := by
      intro x
      have hstar : E.norm (((star f : adjSub E) : E.carrier →L[ℂ] E.carrier)
          ((f : E.carrier →L[ℂ] E.carrier) x)) ≤ ‖star f * f‖ * E.norm x :=
        ((star f * f : adjSub E) : E.carrier →L[ℂ] E.carrier).le_opNorm x
      have hsq : ‖(f : E.carrier →L[ℂ] E.carrier) x‖ ^ 2
          ≤ (Real.sqrt ‖star f * f‖ * ‖x‖) ^ 2 := by
        rw [absNorm_eq ((f : E.carrier →L[ℂ] E.carrier) x), E.norm_sq, inner_apply_star f,
          mul_pow, Real.sq_sqrt hK]
        calc ‖E.inner x (((star f : adjSub E) : E.carrier →L[ℂ] E.carrier)
              ((f : E.carrier →L[ℂ] E.carrier) x))‖
            ≤ E.norm x * E.norm (((star f : adjSub E) : E.carrier →L[ℂ] E.carrier)
              ((f : E.carrier →L[ℂ] E.carrier) x)) := E.norm_inner_le _ _
          _ ≤ E.norm x * (‖star f * f‖ * E.norm x) :=
            mul_le_mul_of_nonneg_left hstar (E.norm_nonneg x)
          _ = ‖star f * f‖ * ‖x‖ ^ 2 := by
            rw [absNorm_eq x]
            ring
      exact le_of_pow_le_pow_left₀ two_ne_zero
        (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x)) hsq
    have hop : ‖(f : E.carrier →L[ℂ] E.carrier)‖ ≤ Real.sqrt ‖star f * f‖ :=
      ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) hb
    calc ‖f‖ * ‖f‖ ≤ Real.sqrt ‖star f * f‖ * Real.sqrt ‖star f * f‖ :=
          mul_self_le_mul_self (norm_nonneg f) hop
      _ = ‖star f * f‖ := Real.mul_self_sqrt hK

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.instCStarRing

end GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp
