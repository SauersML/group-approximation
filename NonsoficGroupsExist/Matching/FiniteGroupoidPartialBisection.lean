import NonsoficGroupsExist.Matching.FiniteGroupoidBisection
import Mathlib.Logic.Equiv.Fintype

/-!
# Completing partial bisections of finite groupoids

A partial bisection selects equally many source and target objects and an
arrow from each selected source to its selected target.  Because every
selected arrow stays inside one connected component, the selected source and
target counts agree separately in each component.  Finite permutation
extension in each component therefore completes the object map to a global
permutation; connectedness supplies arrows on the remaining objects.

This is the exact finite completion used after the centralizer-counting
argument.  It is proved here from finite equivalence extension and the
groupoid laws, with no external groupoid or rigidity input.
-/

namespace NonsoficGroupsExist
namespace FiniteGroupoid

open CategoryTheory

universe u v

variable {C : Type u} [Groupoid.{v} C] [Fintype C]

/-- Connectedness of objects in a groupoid. -/
def connectedSetoid (C : Type u) [Groupoid.{v} C] : Setoid C where
  r X Y := Nonempty (X ⟶ Y)
  iseqv := ⟨fun X ↦ ⟨𝟙 X⟩,
    fun ⟨f⟩ ↦ ⟨inv f⟩,
    fun ⟨f⟩ ⟨g⟩ ↦ ⟨f ≫ g⟩⟩

/-- A bisection defined on only a finite set of source objects. -/
structure PartialBisection (C : Type u) [Groupoid.{v} C] where
  source : Finset C
  target : Finset C
  objEquiv : ↑source ≃ ↑target
  hom : ∀ X : ↑source, X.1 ⟶ (objEquiv X).1

namespace PartialBisection

variable (a : PartialBisection C)

private abbrev Component := Quotient (connectedSetoid C)

private abbrev componentMap : C → Component (C := C) :=
  Quotient.mk (connectedSetoid C)

private abbrev ComponentFiber (q : Component (C := C)) :=
  {X : C // componentMap (C := C) X = q}

private abbrev SourceFiber (q : Component (C := C)) :=
  {X : ↑a.source // componentMap (C := C) X.1 = q}

/-- The selected source objects in one connected component, included into
that component's full object fiber. -/
private def sourceFiberInclusion (q : Component (C := C)) :
    SourceFiber a q → ComponentFiber (C := C) q :=
  fun X ↦ ⟨X.1.1, X.2⟩

/-- The selected targets of source objects in one component.  The partial
bisection arrow proves that the target remains in the same component. -/
private def sourceFiberTarget (q : Component (C := C)) :
    SourceFiber a q → ComponentFiber (C := C) q := fun X ↦ by
  refine ⟨(a.objEquiv X.1).1, ?_⟩
  rw [← X.2]
  exact Quotient.sound ⟨a.hom X.1⟩

private theorem sourceFiberInclusion_injective (q : Component (C := C)) :
    Function.Injective (sourceFiberInclusion a q) := by
  intro X Y hXY
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg Subtype.val hXY

private theorem sourceFiberTarget_injective (q : Component (C := C)) :
    Function.Injective (sourceFiberTarget a q) := by
  intro X Y hXY
  apply Subtype.ext
  apply a.objEquiv.injective
  apply Subtype.ext
  exact congrArg Subtype.val hXY

/-- Complete the selected object matching separately inside one connected
component. -/
private noncomputable def fiberCompletion (q : Component (C := C)) :
    Equiv.Perm (ComponentFiber (C := C) q) :=
  Classical.choose (Equiv.Perm.exists_extending_pair
    (sourceFiberInclusion a q) (sourceFiberTarget a q)
    (sourceFiberInclusion_injective a q) (sourceFiberTarget_injective a q))

private theorem fiberCompletion_spec (q : Component (C := C))
    (X : SourceFiber a q) :
    fiberCompletion a q (sourceFiberInclusion a q X) =
      sourceFiberTarget a q X :=
  Classical.choose_spec (Equiv.Perm.exists_extending_pair
    (sourceFiberInclusion a q) (sourceFiberTarget a q)
    (sourceFiberInclusion_injective a q) (sourceFiberTarget_injective a q)) X

/-- The global object permutation obtained by completing independently in
each connected component. -/
noncomputable def completionObjEquiv : C ≃ C :=
  (Equiv.sigmaFiberEquiv (componentMap (C := C))).symm |>.trans
    ((Equiv.sigmaCongrRight fun q ↦ fiberCompletion a q).trans
      (Equiv.sigmaFiberEquiv (componentMap (C := C))))

theorem completionObjEquiv_component (X : C) :
    componentMap (C := C) (a.completionObjEquiv X) =
      componentMap (C := C) X := by
  rfl

/-- Completion agrees with the prescribed partial object map. -/
theorem completionObjEquiv_apply_of_mem (X : C) (hX : X ∈ a.source) :
    a.completionObjEquiv X = a.objEquiv ⟨X, hX⟩ := by
  let q := componentMap (C := C) X
  let x : SourceFiber a q := ⟨⟨X, hX⟩, rfl⟩
  have hx := fiberCompletion_spec a q x
  exact congrArg Subtype.val hx

/-- Every partial bisection of a finite groupoid extends to a total
bisection.  On unselected objects, an arrow exists because the completed
object permutation stays in the same connected component. -/
noncomputable def complete : Bisection C where
  objEquiv := a.completionObjEquiv
  hom X := by
    by_cases hX : X ∈ a.source
    · exact a.hom ⟨X, hX⟩ ≫
        eqToHom (a.completionObjEquiv_apply_of_mem X hX).symm
    · have hconnected : Nonempty (X ⟶ a.completionObjEquiv X) :=
        Quotient.exact (a.completionObjEquiv_component X).symm
      exact Classical.choice hconnected

/-- On the selected source, completion changes only the definitional target
identification forced by the extended object permutation. -/
theorem complete_hom_of_mem (X : C) (hX : X ∈ a.source) :
    (a.complete).hom X = a.hom ⟨X, hX⟩ ≫
      eqToHom (a.completionObjEquiv_apply_of_mem X hX).symm := by
  simp only [complete, hX, dite_true]

end PartialBisection
end FiniteGroupoid
end NonsoficGroupsExist
