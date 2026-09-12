import Mathlib.GroupTheory.HNNExtension

/-!
# HNN extensions along an isomorphism of bases

`Algebra.HNNPresentation` shows that a group presented by HNN relations *is*
the HNN extension --- but only when the base is literally `PresentedGroup rels`
and the associated subgroups are literally `Subgroup.closure (Set.range …)`.
The towers this development builds are not in that shape: their stages are HNN
extensions of *each other*, and a presentation for a stage arrives as an
isomorphism, not as a definitional identity.

This file closes that gap.  An isomorphism of bases carrying one associated
subgroup onto the other, and intertwining the two identifications, induces an
isomorphism of HNN extensions.  With it, an inductive construction can carry a
presentation up a tower one stage at a time: transport the stage along its
presentation, apply `HNNPresentation.equivPres`, and repeat.

Only the *source* subgroup and the values of the identification enter the
hypotheses.  `B` never appears on its own, because `HNNExtension.lift` asks for
the conjugation identity `t · f a = f (φ a) · t`, in which `B` occurs only as
the codomain of `φ`.
-/

namespace GroupApproximation
namespace HNNCongr

open HNNExtension

variable {G G' : Type} [Group G] [Group G'] {A B : Subgroup G} {A' B' : Subgroup G'}
  (φ : A ≃* B) (φ' : A' ≃* B') (e : G ≃* G')

section Forward

variable (hA : ∀ g : G, g ∈ A ↔ e g ∈ A')

/-- The compatibility of the two identifications: `φ'` on the transported
element is the transport of `φ`. -/
abbrev Intertwines : Prop :=
  ∀ (a : G) (ha : a ∈ A),
    ((φ' ⟨e a, (hA a).1 ha⟩ : B') : G') = e ((φ ⟨a, ha⟩ : B) : G)

variable (hcomm : Intertwines φ φ' e hA)

include hA hcomm in
/-- The conjugation identity `HNNExtension.lift` asks for, in the target
extension. -/
theorem conj_cond (a : A) :
    (HNNExtension.t : HNNExtension G' A' B' φ') *
        (HNNExtension.of.comp (e : G →* G')) (a : G)
      = (HNNExtension.of.comp (e : G →* G')) ((φ a : B) : G) * HNNExtension.t := by
  obtain ⟨a, ha⟩ := a
  have hmem : e a ∈ A' := (hA a).1 ha
  have hconj := HNNExtension.equiv_eq_conj (φ := φ') ⟨e a, hmem⟩
  have hval : ((φ' ⟨e a, hmem⟩ : B') : G') = e ((φ ⟨a, ha⟩ : B) : G) := hcomm a ha
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
  show HNNExtension.t * HNNExtension.of (e a)
    = HNNExtension.of (e ((φ ⟨a, ha⟩ : B) : G)) * HNNExtension.t
  rw [← hval, hconj]
  show HNNExtension.t * HNNExtension.of ((⟨e a, hmem⟩ : A') : G')
    = HNNExtension.t * HNNExtension.of ((⟨e a, hmem⟩ : A') : G') *
        HNNExtension.t⁻¹ * HNNExtension.t
  rw [inv_mul_cancel_right]

include hA hcomm in
/-- The induced map upwards. -/
def congrHom : HNNExtension G A B φ →* HNNExtension G' A' B' φ' :=
  HNNExtension.lift (HNNExtension.of.comp (e : G →* G')) HNNExtension.t
    (conj_cond φ φ' e hA hcomm)

include hA hcomm in
@[simp] theorem congrHom_of (g : G) :
    congrHom φ φ' e hA hcomm (HNNExtension.of g) = HNNExtension.of (e g) := by
  rw [congrHom, HNNExtension.lift_of]
  rfl

include hA hcomm in
@[simp] theorem congrHom_t :
    congrHom φ φ' e hA hcomm (HNNExtension.t : HNNExtension G A B φ)
      = HNNExtension.t := by
  rw [congrHom, HNNExtension.lift_t]

end Forward

/-! ## The inverse

The hypotheses transport backwards along `e.symm`, and the two composites are
the identity because they are the identity on `of` and on `t`, which is what
`HNNExtension.hom_ext` reduces them to. -/

variable (hA : ∀ g : G, g ∈ A ↔ e g ∈ A')

include hA in
theorem symm_mem (g' : G') : g' ∈ A' ↔ e.symm g' ∈ A := by
  rw [hA (e.symm g'), MulEquiv.apply_symm_apply]

variable (hcomm : Intertwines φ φ' e hA)

include hA hcomm in
theorem symm_intertwines : Intertwines φ' φ e.symm (symm_mem e hA) := by
  intro a' ha'
  have hmemA : e.symm a' ∈ A := (symm_mem e hA a').1 ha'
  have h := hcomm (e.symm a') hmemA
  have hsub : (⟨e (e.symm a'), (hA (e.symm a')).1 hmemA⟩ : A') = ⟨a', ha'⟩ :=
    Subtype.ext (e.apply_symm_apply a')
  rw [hsub] at h
  rw [h]
  exact (MulEquiv.symm_apply_apply e _).symm

include hA hcomm in
theorem congr_left (g : G) :
    congrHom φ' φ e.symm (symm_mem e hA) (symm_intertwines φ φ' e hA hcomm)
        (congrHom φ φ' e hA hcomm (HNNExtension.of g))
      = HNNExtension.of g := by
  rw [congrHom_of, congrHom_of, MulEquiv.symm_apply_apply]

include hA hcomm in
theorem congr_comp_symm :
    (congrHom φ' φ e.symm (symm_mem e hA) (symm_intertwines φ φ' e hA hcomm)).comp
        (congrHom φ φ' e hA hcomm) = MonoidHom.id _ := by
  refine HNNExtension.hom_ext ?_ ?_
  · refine MonoidHom.ext fun g => ?_
    rw [MonoidHom.comp_assoc]
    show congrHom φ' φ e.symm (symm_mem e hA) (symm_intertwines φ φ' e hA hcomm)
      (congrHom φ φ' e hA hcomm (HNNExtension.of g)) = _
    rw [congr_left]
    rfl
  · show congrHom φ' φ e.symm (symm_mem e hA) (symm_intertwines φ φ' e hA hcomm)
      (congrHom φ φ' e hA hcomm HNNExtension.t) = _
    rw [congrHom_t, congrHom_t]
    rfl

include hA hcomm in
theorem symm_comp_congr :
    (congrHom φ φ' e hA hcomm).comp
        (congrHom φ' φ e.symm (symm_mem e hA) (symm_intertwines φ φ' e hA hcomm))
      = MonoidHom.id _ := by
  refine HNNExtension.hom_ext ?_ ?_
  · refine MonoidHom.ext fun g' => ?_
    show congrHom φ φ' e hA hcomm
      (congrHom φ' φ e.symm (symm_mem e hA) (symm_intertwines φ φ' e hA hcomm)
        (HNNExtension.of g')) = _
    rw [congrHom_of, congrHom_of, MulEquiv.apply_symm_apply]
    rfl
  · show congrHom φ φ' e hA hcomm
      (congrHom φ' φ e.symm (symm_mem e hA) (symm_intertwines φ φ' e hA hcomm)
        HNNExtension.t) = _
    rw [congrHom_t, congrHom_t]
    rfl

include hA hcomm in
/-- **HNN extensions along an isomorphism of bases.**  An isomorphism carrying
one source subgroup onto the other and intertwining the identifications induces
an isomorphism of the extensions. -/
def congrEquiv : HNNExtension G A B φ ≃* HNNExtension G' A' B' φ' where
  toFun := congrHom φ φ' e hA hcomm
  invFun := congrHom φ' φ e.symm (symm_mem e hA) (symm_intertwines φ φ' e hA hcomm)
  left_inv x :=
    congrArg (fun F : HNNExtension G A B φ →* HNNExtension G A B φ => F x)
      (congr_comp_symm φ φ' e hA hcomm)
  right_inv x :=
    congrArg (fun F : HNNExtension G' A' B' φ' →* HNNExtension G' A' B' φ' => F x)
      (symm_comp_congr φ φ' e hA hcomm)
  map_mul' := map_mul _

end HNNCongr
end GroupApproximation
