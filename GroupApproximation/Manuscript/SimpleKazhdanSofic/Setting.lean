import Mathlib.Dynamics.SymbolicDynamics.Basic
import GroupApproximation.Dynamics.ClopenCrossedProduct
import GroupApproximation.Leavitt.ElementaryGroup
import GroupApproximation.Meta.AxiomGuard

/-!
# The setting of `simple_kazhdan_sofic_group.tex`: subshifts, the shift, the ring and the group

The note at origin/main bf961c128 states its theorem for an infinite minimal subshift `X ⊆ A^ℤ` over
a finite alphabet with shift `T` (tex l.44–46), the ring `R = LC(X, F₂) ⋊_T ℤ` (tex l.73) and the
group `G_X = EL₃(R)` (tex l.48, l.86).  This module fixes those objects once, so that the sections
of the note consume one spelling:

* `subshiftHomeo S`: the shift `(T x)_n = x_{n+1}` of a subshift `S` (tex l.71), over Mathlib's
  `SymbolicDynamics.FullShift.Subshift`;
* `IsMinimal S`: no nonempty proper closed shift-invariant subset (tex l.45);
* `letterIndicator S a`: the indicator `e_a` of the cylinder `{x : x_0 = a}` (tex l.84–85);
* `R S = LC(X, F₂) ⋊_T ℤ` and `G S = EL₃(R S)`.

The definitions are skf-degrees' spelling (the draft `WordProblemDegreeStatements`), moved here so
that the statement of the main theorem and the word-problem section share them.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

open SymbolicDynamics.FullShift Set

section Subshift

variable {A : Type} [TopologicalSpace A]

/-- The shift homeomorphism of a subshift, `(T x)_n = x_{n+1}` (tex l.71). -/
def subshiftHomeo (S : Subshift A ℤ) : S.carrier ≃ₜ S.carrier where
  toFun x := ⟨shift 1 x.1, S.mapsTo 1 x.2⟩
  invFun x := ⟨shift (-1) x.1, S.mapsTo (-1) x.2⟩
  left_inv x := by
    apply Subtype.ext
    funext n
    show x.1 (1 + (-1 + n)) = x.1 n
    exact congrArg x.1 (by omega)
  right_inv x := by
    apply Subtype.ext
    funext n
    show x.1 (-1 + (1 + n)) = x.1 n
    exact congrArg x.1 (by omega)
  continuous_toFun :=
    ((continuous_shift 1 : Continuous (shift (1 : ℤ) : (ℤ → A) → ℤ → A)).comp
      continuous_subtype_val).subtype_mk fun x => S.mapsTo 1 x.2
  continuous_invFun :=
    ((continuous_shift (-1) : Continuous (shift (-1 : ℤ) : (ℤ → A) → ℤ → A)).comp
      continuous_subtype_val).subtype_mk fun x => S.mapsTo (-1) x.2

/-- A subshift is minimal if it has no nonempty proper closed shift-invariant subset (tex l.45). -/
def IsMinimal (S : Subshift A ℤ) : Prop :=
  ∀ C : Set (ℤ → A), IsClosed C → C ⊆ S.carrier → (∀ g : ℤ, MapsTo (shift g) C C) →
    C = ∅ ∨ C = S.carrier

/-- The letter indicator `e_a` of the cylinder `{x : x_0 = a}` (tex l.84). -/
noncomputable def letterIndicator [DiscreteTopology A] [DecidableEq A] (S : Subshift A ℤ) (a : A) :
    LocallyConstant S.carrier (ZMod 2) where
  toFun x := if x.1 0 = a then 1 else 0
  isLocallyConstant :=
    ((IsLocallyConstant.iff_continuous (fun x : S.carrier => x.1 0)).2
      ((continuous_apply (0 : ℤ)).comp continuous_subtype_val)).comp
      fun b => if b = a then (1 : ZMod 2) else 0

end Subshift

section Group

variable {A : Type} [TopologicalSpace A]

/-- The ring `R = LC(X, F₂) ⋊_T ℤ` (tex l.73). -/
abbrev R (S : Subshift A ℤ) : Type := ClopenCrossedProduct (subshiftHomeo S) (ZMod 2)

/-- The group `G_X = EL₃(R)` (tex l.46 and l.86). -/
abbrev G (S : Subshift A ℤ) : Type := ↥(elementaryGroup (Fin 3) (R S))

end Group

end SimpleKazhdanSofic
end GroupApproximation
