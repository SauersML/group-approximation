import GroupApproximation.Steinberg.A2Kazhdan
import GroupApproximation.Steinberg.RootFiltration
import GroupApproximation.Steinberg.RootActions
import GroupApproximation.PropertyT.ClassTwoNormalForm

/-!
# Finite root control in the rank-three Steinberg group

For a finite free characteristic-two algebra, this file constructs the finite
set of unit and free-generator root elements that is used in the direct
Steinberg proof of property `(T)`.  It also proves the algebraic normalization
facts needed to compare displacement by this finite set with displacement by
an entire two-root plane.

Nothing here factors through the elementary quotient.  In particular, none
of the results assumes that the canonical Steinberg projection is injective
or that its unstable `K₂` kernel is central.
-/

namespace GroupApproximation
namespace SteinbergGroup

open FreeAlgebraDegree
open scoped commutatorElement

noncomputable section

variable (X : Type*) [Fintype X]

omit [Fintype X] in
/-- An adjacent Steinberg root normalizes the plane formed by the two roots
with a common terminal index. -/
theorem x_mem_normalizer_columnPlane
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a : FreeAlgebra (ZMod 2) X) :
    x i j hij a ∈ Subgroup.normalizer
      (rootSubgroup i k hik ⊔ rootSubgroup j k hjk :
        Subgroup (SteinbergGroup (Fin 3) (FreeAlgebra (ZMod 2) X))) := by
  let A := a2System (R := FreeAlgebra (ZMod 2) X)
  let Xij : Subgroup (SteinbergGroup (Fin 3) (FreeAlgebra (ZMod 2) X)) :=
    rootSubgroup i j hij
  let Xjk : Subgroup (SteinbergGroup (Fin 3) (FreeAlgebra (ZMod 2) X)) :=
    rootSubgroup j k hjk
  let Xik : Subgroup (SteinbergGroup (Fin 3) (FreeAlgebra (ZMod 2) X)) :=
    rootSubgroup i k hik
  have hYX : ⁅Xij, Xjk⁆ ≤ Xik := by
    apply Subgroup.commutator_le.mpr
    intro u hu v hv
    exact A.commutator_mem i j k hij hjk hik u hu v hv
  have hYZ : ⁅Xij, Xik⁆ ≤ Xik := by
    apply Subgroup.commutator_le.mpr
    intro u hu v hv
    have hcomm : Commute u v :=
      A.commute i j i k hij hik hij.symm hik.symm u hu v hv
    rw [commutatorElement_eq_one_iff_commute.mpr hcomm]
    exact Xik.one_mem
  have hnormal : Xij ≤ Subgroup.normalizer (Xjk ⊔ Xik :
      Subgroup (SteinbergGroup (Fin 3) (FreeAlgebra (ZMod 2) X))) :=
    ClassTwoNormalForm.le_normalizer_sup Xjk Xij Xik hYX hYZ
  have hmem : x i j hij a ∈ Xij := ⟨a, rfl⟩
  simpa only [sup_comm] using hnormal hmem

/-- A fixed exhaustive enumeration of the finite free-generator alphabet. -/
def finiteGeneratorEnumeration : Fin (Fintype.card X) ≃ X :=
  (Fintype.equivFin X).symm

/-- Coefficients used by the finite Steinberg control set: the unit and the
chosen enumeration of the free algebra generators. -/
def finiteControlCoefficient
    (q : Option (Fin (Fintype.card X))) : FreeAlgebra (ZMod 2) X :=
  match q with
  | none => 1
  | some q => FreeAlgebra.ι (ZMod 2) (finiteGeneratorEnumeration X q)

/-- One unit-or-generator element in one of the six Steinberg roots. -/
def finiteControlElement
    (p : A2Root × Option (Fin (Fintype.card X))) :
    SteinbergGroup (Fin 3) (FreeAlgebra (ZMod 2) X) :=
  x p.1.1.1 p.1.1.2 p.1.2 (finiteControlCoefficient X p.2)

/-- Unit and free-generator coefficients in every ordered Steinberg root. -/
def finiteControlSet :
    Finset (SteinbergGroup (Fin 3) (FreeAlgebra (ZMod 2) X)) := by
  classical
  exact (Finset.univ : Finset
    (A2Root × Option (Fin (Fintype.card X)))).image
      (finiteControlElement X)

theorem finiteControlElement_mem
    (p : A2Root × Option (Fin (Fintype.card X))) :
    finiteControlElement X p ∈ finiteControlSet X := by
  classical
  exact Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩

/-- Every finite control element normalizes either common-terminal-index
plane whenever its root is one of the two plane roots or either adjacent
root.  The four cases are exposed separately for the analytic estimate. -/
theorem finiteControl_normalizes_columnPlanes
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (q : Option (Fin (Fintype.card X))) :
    let H : Subgroup (SteinbergGroup (Fin 3) (FreeAlgebra (ZMod 2) X)) :=
      rootSubgroup i k hik ⊔ rootSubgroup j k hjk
    x i j hij (finiteControlCoefficient X q) ∈ Subgroup.normalizer H ∧
      x j i hij.symm (finiteControlCoefficient X q) ∈
        Subgroup.normalizer H ∧
      x i k hik (finiteControlCoefficient X q) ∈
        Subgroup.normalizer H ∧
      x j k hjk (finiteControlCoefficient X q) ∈
        Subgroup.normalizer H := by
  dsimp only
  refine ⟨x_mem_normalizer_columnPlane X i j k hij hik hjk _, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa only [sup_comm] using
      x_mem_normalizer_columnPlane X j i k hij.symm hjk hik
        (finiteControlCoefficient X q)
  · apply (rootSubgroup i k hik ⊔ rootSubgroup j k hjk).le_normalizer
    exact (show rootSubgroup i k hik ≤
      rootSubgroup i k hik ⊔ rootSubgroup j k hjk from le_sup_left)
      ⟨finiteControlCoefficient X q, rfl⟩
  · apply (rootSubgroup i k hik ⊔ rootSubgroup j k hjk).le_normalizer
    exact (show rootSubgroup j k hjk ≤
      rootSubgroup i k hik ⊔ rootSubgroup j k hjk from le_sup_right)
      ⟨finiteControlCoefficient X q, rfl⟩

end
end SteinbergGroup
end GroupApproximation
