import GroupApproximation.CharClass.BundleLocal

/-!
# Complex vector bundles in the projection model, XXXIV: the total space over an
open set

The total-space twin of `BundleProjOver`.  `Total (p.restrictTo U)` and the part
of `Total p` lying over `U` are the same space but not the same subtype: the
first sits inside `↥U × (ι → ℂ)` and the second inside `Total p`, hence inside
`X × (ι → ℂ)`.

Presenting it as a **subset**, and as an **open** one when `U` is open, is what
lets a relative-cohomology argument reach it: excision applies to an open
subspace, not to the image of a map that happens to be injective.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59

namespace Bundle

section TotalOver

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]

/-- The part of `E(p)` lying over `U`. -/
def totalOverSet (p : Bundle X ι) (U : Set X) : Set (Total p) := (totalPi p) ⁻¹' U

theorem mem_totalOverSet_iff {p : Bundle X ι} {U : Set X} {v : Total p} :
    v ∈ totalOverSet p U ↔ (v : X × (ι → ℂ)).1 ∈ U := Iff.rfl

/-- **It is open when `U` is**, which is what excision needs. -/
theorem isOpen_totalOverSet (p : Bundle X ι) {U : Set X} (hU : IsOpen U) :
    IsOpen (totalOverSet p U) :=
  hU.preimage (totalPi p).continuous

theorem totalInclOn_mem (p : Bundle X ι) (U : Set X) (w : Total (p.restrictTo U)) :
    ((((w : ↥U × (ι → ℂ)).1 : X), (w : ↥U × (ι → ℂ)).2) : X × (ι → ℂ)) ∈ totalSet p :=
  w.2

/-- **The inclusion of the restricted total space**, forgetting that the base
point lies in `U`. -/
def totalInclOn (p : Bundle X ι) (U : Set X) : C(Total (p.restrictTo U), Total p) where
  toFun w := ⟨(((w : ↥U × (ι → ℂ)).1 : X), (w : ↥U × (ι → ℂ)).2), totalInclOn_mem p U w⟩
  continuous_toFun :=
    (((continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))).prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _

theorem totalInclOn_apply (p : Bundle X ι) (U : Set X) (w : Total (p.restrictTo U)) :
    ((totalInclOn p U w : Total p) : X × (ι → ℂ))
      = (((w : ↥U × (ι → ℂ)).1 : X), (w : ↥U × (ι → ℂ)).2) := rfl

theorem totalInclOn_mem_totalOverSet (p : Bundle X ι) (U : Set X)
    (w : Total (p.restrictTo U)) : totalInclOn p U w ∈ totalOverSet p U :=
  (w : ↥U × (ι → ℂ)).1.2

theorem totalInclOn_injective (p : Bundle X ι) (U : Set X) :
    Function.Injective (totalInclOn p U) := by
  intro w w' h
  have h' := congrArg (fun v : Total p => (v : X × (ι → ℂ))) h
  rw [totalInclOn_apply, totalInclOn_apply] at h'
  apply Subtype.ext
  refine Prod.ext (Subtype.ext (congrArg (fun q : X × (ι → ℂ) => q.1) h'))
    (congrArg (fun q : X × (ι → ℂ) => q.2) h')

theorem totalOverHomeo_invFun_mem (p : Bundle X ι) (U : Set X) (v : ↥(totalOverSet p U)) :
    (((⟨((v : Total p) : X × (ι → ℂ)).1, v.2⟩ : ↥U),
      ((v : Total p) : X × (ι → ℂ)).2) : ↥U × (ι → ℂ)) ∈ totalSet (p.restrictTo U) :=
  (v : Total p).2

/-- **The part of `E(p)` over `U` is `E(p|_U)`, over the base.** -/
noncomputable def totalOverHomeo (p : Bundle X ι) (U : Set X) :
    Total (p.restrictTo U) ≃ₜ ↥(totalOverSet p U) where
  toFun w := ⟨totalInclOn p U w, totalInclOn_mem_totalOverSet p U w⟩
  invFun v := ⟨(⟨((v : Total p) : X × (ι → ℂ)).1, v.2⟩,
      ((v : Total p) : X × (ι → ℂ)).2), totalOverHomeo_invFun_mem p U v⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := ((totalInclOn p U).continuous).subtype_mk _
  continuous_invFun :=
    ((((continuous_fst.comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _).prodMk
        (continuous_snd.comp
          (continuous_subtype_val.comp continuous_subtype_val)))).subtype_mk _

theorem totalOverHomeo_over_base (p : Bundle X ι) (U : Set X) (w : Total (p.restrictTo U)) :
    (((totalOverHomeo p U w : Total p)) : X × (ι → ℂ)).1
      = ((totalPi (p.restrictTo U) w : ↥U) : X) := rfl

/-- **The inclusion is a map of punctured pairs**, in both directions. -/
theorem totalInclOn_mem_puncturedSet_iff (p : Bundle X ι) (U : Set X)
    (w : Total (p.restrictTo U)) :
    ((totalInclOn p U w : Total p) : X × (ι → ℂ)) ∈ puncturedSet p
      ↔ (w : ↥U × (ι → ℂ)) ∈ puncturedSet (p.restrictTo U) :=
  ⟨fun h => ⟨w.2, h.2⟩, fun h => ⟨totalInclOn_mem p U w, h.2⟩⟩

theorem totalInclOn_preimage_puncturedSet (p : Bundle X ι) (U : Set X) :
    {w : Total (p.restrictTo U) |
        ((totalInclOn p U w : Total p) : X × (ι → ℂ)) ∈ puncturedSet p}
      = {w : Total (p.restrictTo U) | (w : ↥U × (ι → ℂ)) ∈ puncturedSet (p.restrictTo U)} := by
  ext w
  exact totalInclOn_mem_puncturedSet_iff p U w

end TotalOver

end Bundle

end CharClass
end GroupApproximation
