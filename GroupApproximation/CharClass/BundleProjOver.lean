import GroupApproximation.CharClass.BundleLocal

/-!
# Complex vector bundles in the projection model, XX: the part over an open set

`Proj (p.restrictTo U)` and the part of `Proj p` lying over `U` are the same
space, but not the same subtype: the first sits inside `↥U × Matrix ι ι ℂ` and
the second inside `Proj p`, hence inside `X × Matrix ι ι ℂ`.  Every trivialisation
in this lane is stated in the first form, and a cover induction over the base
produces the second, so the comparison has to exist somewhere.  It is pure
point-set: the four conditions cutting out `projSet` mention the base point only
through `p` at it, and `p.restrictTo U` at a point of `U` **is** `p` at its
image.

`restrictTo_plusOne` records the other half of the bookkeeping: restricting and
adding a trivial line commute, on the nose.

## Main declarations

* `projOverSet` — the part of `P(p)` over `U`, as a preimage.
* `projOverHomeo` — **the comparison**, over the base.
* `restrictTo_plusOne` — `(p|_U) ⊕ 1 = (p ⊕ 1)|_U`, by `rfl`.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59

namespace Bundle

section ProjOver

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]

/-- **Restricting and adding a trivial line commute.** -/
theorem restrictTo_plusOne [DecidableEq ι] (p : Bundle X ι) (U : Set X) :
    (p.restrictTo U).plusOne = (p.plusOne).restrictTo U := rfl

/-- The part of `P(p)` lying over `U`. -/
def projOverSet (p : Bundle X ι) (U : Set X) : Set (Proj p) := (projPi p) ⁻¹' U

theorem mem_projOverSet_iff {p : Bundle X ι} {U : Set X} {z : Proj p} :
    z ∈ projOverSet p U ↔ (z : X × Matrix ι ι ℂ).1 ∈ U := Iff.rfl

theorem projOverHomeo_toFun_mem (p : Bundle X ι) (U : Set X)
    (w : Proj (p.restrictTo U)) :
    ((((w : ↥U × Matrix ι ι ℂ).1 : X), (w : ↥U × Matrix ι ι ℂ).2) : X × Matrix ι ι ℂ)
      ∈ projSet p :=
  w.2

theorem projOverHomeo_invFun_mem (p : Bundle X ι) (U : Set X)
    (z : ↥(projOverSet p U)) :
    (((⟨((z : Proj p) : X × Matrix ι ι ℂ).1, z.2⟩ : ↥U),
      ((z : Proj p) : X × Matrix ι ι ℂ).2) : ↥U × Matrix ι ι ℂ)
      ∈ projSet (p.restrictTo U) :=
  (z : Proj p).2

/-- **The part of `P(p)` over `U` is `P(p|_U)`, over the base.**  Both sides
carry the same matrix at the same point; only the ambient subtype differs. -/
def projOverHomeo (p : Bundle X ι) (U : Set X) :
    Proj (p.restrictTo U) ≃ₜ ↥(projOverSet p U) where
  toFun w :=
    ⟨⟨(((w : ↥U × Matrix ι ι ℂ).1 : X), (w : ↥U × Matrix ι ι ℂ).2),
        projOverHomeo_toFun_mem p U w⟩, (w : ↥U × Matrix ι ι ℂ).1.2⟩
  invFun z :=
    ⟨(⟨((z : Proj p) : X × Matrix ι ι ℂ).1, z.2⟩,
        ((z : Proj p) : X × Matrix ι ι ℂ).2), projOverHomeo_invFun_mem p U z⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    ((((continuous_subtype_val.comp
      (continuous_fst.comp continuous_subtype_val))).prodMk
        (continuous_snd.comp continuous_subtype_val)).subtype_mk _).subtype_mk _
  continuous_invFun :=
    ((((continuous_fst.comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _)).prodMk
        (continuous_snd.comp
          (continuous_subtype_val.comp continuous_subtype_val))).subtype_mk _

/-- **The comparison is over the base.**  By `rfl`, so it composes with a
projection square with nothing to discharge. -/
theorem projOverHomeo_over_base (p : Bundle X ι) (U : Set X)
    (w : Proj (p.restrictTo U)) :
    ((projOverHomeo p U w : Proj p) : X × Matrix ι ι ℂ).1
      = ((projPi (p.restrictTo U) w : ↥U) : X) := rfl

/-- And the matrix is unchanged. -/
theorem projOverHomeo_snd (p : Bundle X ι) (U : Set X) (w : Proj (p.restrictTo U)) :
    ((projOverHomeo p U w : Proj p) : X × Matrix ι ι ℂ).2
      = (w : ↥U × Matrix ι ι ℂ).2 := rfl

/-! ### The inclusion, as a bundled map -/

theorem projInclOn_mem (p : Bundle X ι) (U : Set X) (w : Proj (p.restrictTo U)) :
    ((((w : ↥U × Matrix ι ι ℂ).1 : X), (w : ↥U × Matrix ι ι ℂ).2) : X × Matrix ι ι ℂ)
      ∈ projSet p :=
  w.2

/-- **The inclusion of the restricted projectivisation**, forgetting that the
base point lies in `U`.  The mirror of `totalInclOn`. -/
def projInclOn (p : Bundle X ι) (U : Set X) : C(Proj (p.restrictTo U), Proj p) where
  toFun w := ⟨(((w : ↥U × Matrix ι ι ℂ).1 : X), (w : ↥U × Matrix ι ι ℂ).2),
    projInclOn_mem p U w⟩
  continuous_toFun :=
    (((continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))).prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _

theorem projInclOn_apply (p : Bundle X ι) (U : Set X) (w : Proj (p.restrictTo U)) :
    ((projInclOn p U w : Proj p) : X × Matrix ι ι ℂ)
      = (((w : ↥U × Matrix ι ι ℂ).1 : X), (w : ↥U × Matrix ι ι ℂ).2) := rfl

theorem projInclOn_over_base (p : Bundle X ι) (U : Set X) (w : Proj (p.restrictTo U)) :
    projPi p (projInclOn p U w) = ((projPi (p.restrictTo U) w : ↥U) : X) := rfl

theorem projInclOn_mem_projOverSet (p : Bundle X ι) (U : Set X)
    (w : Proj (p.restrictTo U)) : projInclOn p U w ∈ projOverSet p U :=
  (w : ↥U × Matrix ι ι ℂ).1.2

theorem projInclOn_injective (p : Bundle X ι) (U : Set X) :
    Function.Injective (projInclOn p U) := by
  intro w w' h
  have h' := congrArg (fun v : Proj p => (v : X × Matrix ι ι ℂ)) h
  rw [projInclOn_apply, projInclOn_apply] at h'
  apply Subtype.ext
  refine Prod.ext (Subtype.ext (congrArg (fun q : X × Matrix ι ι ℂ => q.1) h'))
    (congrArg (fun q : X × Matrix ι ι ℂ => q.2) h')

/-- **Including into the whole projectivisation commutes with the hyperplane
inclusion.**  By `rfl`: `restrictTo_plusOne` makes the two sides typecheck
against each other with no transport, and both carry the same padded matrix over
the same base point. -/
theorem projInclOn_projIncl [DecidableEq ι] (p : Bundle X ι) (U : Set X)
    (w : Proj (p.restrictTo U)) :
    projInclOn p.plusOne U (projIncl (p.restrictTo U) w)
      = projIncl p (projInclOn p U w) := rfl

end ProjOver

end Bundle

end CharClass
end GroupApproximation
