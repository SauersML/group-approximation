import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Renumbering the generators of a presentation

`Computability.PresentationCodes` numbers the generators of a finite
presentation by `Fin (n + 1)`, while every presentation this development
*builds* carries the generator type it was built with: `Fin 3` for the Boone
base, and one `Option` for each stable letter adjoined by
`Algebra.HNNPresentation`, so a tower of `k` HNN steps over the base presents a
group on `Option^[k] (Fin 3)`.

Nothing about a presented group depends on the names of its generators, and
this file says so: `congrEquiv` renumbers along any equivalence of generator
types, and `optionFinEquiv` is the one renumbering the towers actually need,
`Option (Fin n) ≃ Fin (n + 1)`.

The construction is by hand rather than through `QuotientGroup.congr` and a
lemma about the image of a normal closure.  Both maps are
`PresentedGroup.toGroup` applied to the relabelled generators, and the two
composites are the identity because they are the identity on generators, which
`PresentedGroup.ext` reduces them to.  That route needs no fact about normal
closures at all, only that a relabelled relator is a relator.
-/

namespace GroupApproximation
namespace PresentedGroupRelabel

variable {α β : Type}

/-- The relabelling map on free groups. -/
abbrev relabel (e : α → β) : FreeGroup α →* FreeGroup β := FreeGroup.map e

/-- The relabelled relator set. -/
def relabelRels (e : α → β) (s : Set (FreeGroup α)) : Set (FreeGroup β) :=
  relabel e '' s

theorem mem_relabelRels {e : α → β} {s : Set (FreeGroup α)} {r : FreeGroup α}
    (hr : r ∈ s) : relabel e r ∈ relabelRels e s :=
  ⟨r, hr, rfl⟩

/-- A relabelled relator dies in the relabelled presentation. -/
theorem relabelRels_mk (e : α → β) (s : Set (FreeGroup α)) {r : FreeGroup α}
    (hr : r ∈ s) :
    PresentedGroup.mk (relabelRels e s) (relabel e r) = 1 :=
  PresentedGroup.mk_eq_one_iff.2 (Subgroup.subset_normalClosure (mem_relabelRels hr))

/-- Sending each generator to the generator with the relabelled name carries
relators to relators. -/
theorem toGroup_cond (e : α → β) (s : Set (FreeGroup α)) :
    ∀ r ∈ s, FreeGroup.lift
      (fun a : α => (PresentedGroup.of (e a) : PresentedGroup (relabelRels e s))) r = 1 := by
  intro r hr
  have hcomp : FreeGroup.lift
      (fun a : α => (PresentedGroup.of (e a) : PresentedGroup (relabelRels e s)))
      = (PresentedGroup.mk (relabelRels e s)).comp (relabel e) := by
    refine FreeGroup.ext_hom _ _ fun a => ?_
    simp [PresentedGroup.of, PresentedGroup.mk]
  rw [hcomp, MonoidHom.comp_apply]
  exact relabelRels_mk e s hr

/-- The forward relabelling homomorphism. -/
def relabelHom (e : α → β) (s : Set (FreeGroup α)) :
    PresentedGroup s →* PresentedGroup (relabelRels e s) :=
  PresentedGroup.toGroup (toGroup_cond e s)

@[simp] theorem relabelHom_of (e : α → β) (s : Set (FreeGroup α)) (a : α) :
    relabelHom e s (PresentedGroup.of a) = PresentedGroup.of (e a) :=
  PresentedGroup.toGroup.of _

/-- Sending each generator to the generator with the *un*-relabelled name
carries relabelled relators to `1`: composing with the relabelling turns the
map into `PresentedGroup.mk` itself. -/
theorem toGroup_cond_symm (e : α ≃ β) (s : Set (FreeGroup α)) :
    ∀ r' ∈ relabelRels (e : α → β) s,
      FreeGroup.lift
        (fun b : β => (PresentedGroup.of (e.symm b) : PresentedGroup s)) r' = 1 := by
  rintro - ⟨r, hr, rfl⟩
  have hcomp :
      (FreeGroup.lift
        (fun b : β => (PresentedGroup.of (e.symm b) : PresentedGroup s))).comp
          (relabel (e : α → β)) = PresentedGroup.mk s := by
    refine FreeGroup.ext_hom _ _ fun a => ?_
    simp [PresentedGroup.of, PresentedGroup.mk]
  have hr' := congrArg (fun F : FreeGroup α →* PresentedGroup s => F r) hcomp
  simp only [MonoidHom.comp_apply] at hr'
  rw [hr']
  exact PresentedGroup.mk_eq_one_iff.2 (Subgroup.subset_normalClosure hr)

/-- The backward relabelling homomorphism. -/
def relabelHomSymm (e : α ≃ β) (s : Set (FreeGroup α)) :
    PresentedGroup (relabelRels (e : α → β) s) →* PresentedGroup s :=
  PresentedGroup.toGroup (toGroup_cond_symm e s)

@[simp] theorem relabelHomSymm_of (e : α ≃ β) (s : Set (FreeGroup α)) (b : β) :
    relabelHomSymm e s (PresentedGroup.of b) = PresentedGroup.of (e.symm b) :=
  PresentedGroup.toGroup.of _

theorem relabel_symm_comp (e : α ≃ β) (s : Set (FreeGroup α)) :
    (relabelHomSymm e s).comp (relabelHom (e : α → β) s) = MonoidHom.id _ := by
  refine PresentedGroup.ext fun a => ?_
  rw [MonoidHom.comp_apply, relabelHom_of, relabelHomSymm_of, MonoidHom.id_apply,
    Equiv.symm_apply_apply]

theorem relabel_comp_symm (e : α ≃ β) (s : Set (FreeGroup α)) :
    (relabelHom (e : α → β) s).comp (relabelHomSymm e s) = MonoidHom.id _ := by
  refine PresentedGroup.ext fun b => ?_
  rw [MonoidHom.comp_apply, relabelHomSymm_of, relabelHom_of, MonoidHom.id_apply,
    Equiv.apply_symm_apply]

/-- **Renumbering the generators of a presentation.**  A presented group does
not depend on the names of its generators. -/
def congrEquiv (e : α ≃ β) (s : Set (FreeGroup α)) :
    PresentedGroup s ≃* PresentedGroup (relabelRels (e : α → β) s) where
  toFun := relabelHom (e : α → β) s
  invFun := relabelHomSymm e s
  left_inv x :=
    congrArg (fun F : PresentedGroup s →* PresentedGroup s => F x) (relabel_symm_comp e s)
  right_inv x :=
    congrArg (fun F : PresentedGroup (relabelRels (e : α → β) s) →*
      PresentedGroup (relabelRels (e : α → β) s) => F x) (relabel_comp_symm e s)
  map_mul' := map_mul _

/-- Relabelling commutes with `PresentedGroup.mk`. -/
theorem relabelHom_mk (e : α → β) (s : Set (FreeGroup α)) (v : FreeGroup α) :
    relabelHom e s (PresentedGroup.mk s v)
      = PresentedGroup.mk (relabelRels e s) (relabel e v) := by
  have h : (relabelHom e s).comp (PresentedGroup.mk s)
      = (PresentedGroup.mk (relabelRels e s)).comp (relabel e) := by
    refine FreeGroup.ext_hom _ _ fun a => ?_
    simp only [MonoidHom.comp_apply]
    exact relabelHom_of e s a
  exact congrArg (fun F : FreeGroup α →* PresentedGroup (relabelRels e s) => F v) h

/-- **A relabelled word dies exactly when the original does.**  This is what
lets a triviality statement be moved between a presentation and its
renumbering. -/
theorem mk_relabel_eq_one_iff (e : α ≃ β) (s : Set (FreeGroup α)) (v : FreeGroup α) :
    PresentedGroup.mk (relabelRels (e : α → β) s) (relabel (e : α → β) v) = 1
      ↔ PresentedGroup.mk s v = 1 := by
  rw [← relabelHom_mk]
  constructor
  · intro h
    have h' := congrArg (relabelHomSymm e s) h
    rwa [← MonoidHom.comp_apply, relabel_symm_comp, MonoidHom.id_apply, map_one] at h'
  · intro h
    rw [h, map_one]

/-! ## The numbering the towers need

Each HNN step of `Algebra.HNNPresentation` wraps the generator type in one
`Option`, so a tower over a base numbered by `Fin n` is numbered by
`Option^[k] (Fin n)`.  `Option (Fin n) ≃ Fin (n + 1)` is Mathlib's
`finSuccEquiv` read backwards, and iterating it renumbers the whole tower. -/

/-- One `Option`, absorbed into the numbering. -/
def optionFinEquiv (n : ℕ) : Option (Fin n) ≃ Fin (n + 1) := (finSuccEquiv n).symm

@[simp] theorem optionFinEquiv_none (n : ℕ) : optionFinEquiv n none = 0 := rfl

@[simp] theorem optionFinEquiv_some (n : ℕ) (i : Fin n) :
    optionFinEquiv n (some i) = i.succ := rfl

/-- One `Option`, numbered in append order: the old generators retain indices
`0, …, n-1`, while `none` is the new final generator `n`.  This is the
numbering used by `FreeEdgeTowerCode.edgeCode`. -/
def optionFinAppendEquiv (n : ℕ) : Option (Fin n) ≃ Fin (n + 1) :=
  (optionFinEquiv n).trans (finRotate (n + 1)).symm

@[simp] theorem optionFinAppendEquiv_none (n : ℕ) :
    optionFinAppendEquiv n none = Fin.last n := by
  apply (finRotate (n + 1)).injective
  simp [optionFinAppendEquiv]

@[simp] theorem optionFinAppendEquiv_some (n : ℕ) (i : Fin n) :
    optionFinAppendEquiv n (some i) = i.castSucc := by
  apply (finRotate (n + 1)).injective
  simp only [optionFinAppendEquiv, Equiv.trans_apply, Equiv.apply_symm_apply,
    optionFinEquiv_some]
  apply Fin.ext
  rw [coe_finRotate_of_ne_last (Fin.castSucc_lt_last i).ne]
  rfl

/-- `k` `Option`s over `Fin n`, as a generator type. -/
def OptionIter (α : Type) : ℕ → Type
  | 0 => α
  | k + 1 => Option (OptionIter α k)

/-- **The tower numbering.**  A generator type built by wrapping `Fin n` in `k`
`Option`s is `Fin (n + k)`. -/
def optionIterFinEquiv (n : ℕ) : ∀ k : ℕ, OptionIter (Fin n) k ≃ Fin (n + k)
  | 0 => Equiv.refl _
  | k + 1 =>
      (Equiv.optionCongr (optionIterFinEquiv n k)).trans (optionFinEquiv (n + k))

end PresentedGroupRelabel
end GroupApproximation
