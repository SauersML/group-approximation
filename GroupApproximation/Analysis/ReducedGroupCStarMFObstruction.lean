import GroupApproximation.Analysis.ReducedGroupCStarTrace
import GroupApproximation.Sofic.NormMFResidualDetector

/-!
# Reduced group C⋆-algebras and norm-matrix-corona obstructions

This file records the older ultraproduct unitary-restriction interface needed
by downstream residual arguments.  The genuine norm-matrix C-star corona and
the general `IsMFAlgebra` API are now formalized separately in
`Analysis.NormMatrixCorona` and `Analysis.MFAlgebra`.
-/

namespace GroupApproximation

open ReducedGroupCStarTrace

noncomputable section

universe u

variable (G : Type u) [Group G]

local instance : DecidableEq G := Classical.decEq G

/-- The concrete closed regular-representation algebra carries its canonical
complex C-star-algebra structure.  This instance belongs with the concrete
object, rather than in a downstream comparison of MF definitions. -/
noncomputable instance reducedGroupCStarCStarAlgebra :
    CStarAlgebra (ReducedGroupCStar G) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace :=
    (StarSubalgebra.isClosed_topologicalClosure
      (StarAlgebra.adjoin ℂ
        (Set.range (leftRegularOperator G)))).completeSpace_coe
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-- The concrete reduced group C-star algebra is nontrivial.  Evaluate the
zero and identity operators on the identity point mass to separate them. -/
noncomputable instance reducedGroupCStarNontrivial :
    Nontrivial (ReducedGroupCStar G) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have heval := congrArg
    (fun T : ReducedGroupCStar G ↦
      ((T : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)) 1) h
  simp [deltaOne] at heval

/-- The left regular operator inside the concrete reduced group C⋆-algebra. -/
def reducedLeftRegular (g : G) : ReducedGroupCStar G :=
  ⟨leftRegularOperator G g,
    StarSubalgebra.le_topologicalClosure _
      (StarAlgebra.subset_adjoin ℂ (Set.range (leftRegularOperator G)) ⟨g, rfl⟩)⟩

@[simp] theorem reducedLeftRegular_apply (g : G) (f : GroupHilbert G) (x : G) :
    (reducedLeftRegular G g : GroupHilbert G →L[ℂ] GroupHilbert G) f x =
      f (g⁻¹ * x) := rfl

theorem reducedLeftRegular_mul (g h : G) :
    reducedLeftRegular G (g * h) = reducedLeftRegular G g * reducedLeftRegular G h := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext x
  change f ((g * h)⁻¹ * x) = f (h⁻¹ * (g⁻¹ * x))
  rw [mul_inv_rev, mul_assoc]

@[simp] theorem reducedLeftRegular_one : reducedLeftRegular G 1 = 1 := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext x
  change f (1⁻¹ * x) = f x
  rw [inv_one, one_mul]

theorem star_reducedLeftRegular (g : G) :
    star (reducedLeftRegular G g) = reducedLeftRegular G g⁻¹ := by
  apply Subtype.ext
  change star (leftRegularOperator G g) = leftRegularOperator G g⁻¹
  rw [ContinuousLinearMap.star_eq_adjoint]
  change ContinuousLinearMap.adjoint
    (leftRegular G g : GroupHilbert G →L[ℂ] GroupHilbert G) = _
  rw [LinearIsometryEquiv.adjoint_eq_symm]
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext x
  change f (g * x) = f ((g⁻¹)⁻¹ * x)
  rw [inv_inv]

def reducedLeftRegularUnitary (g : G) : unitary (ReducedGroupCStar G) :=
  ⟨reducedLeftRegular G g, by
    constructor
    · rw [star_reducedLeftRegular, ← reducedLeftRegular_mul, inv_mul_cancel,
        reducedLeftRegular_one]
    · rw [star_reducedLeftRegular, ← reducedLeftRegular_mul, mul_inv_cancel,
        reducedLeftRegular_one]⟩

def reducedLeftRegularUnitaryHom : G →* unitary (ReducedGroupCStar G) where
  toFun := reducedLeftRegularUnitary G
  map_one' := by apply Subtype.ext; exact reducedLeftRegular_one G
  map_mul' g h := by apply Subtype.ext; exact reducedLeftRegular_mul G g h

theorem reducedLeftRegular_deltaOne (g : G) :
    (reducedLeftRegular G g : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G) =
      lp.single 2 g 1 := by
  classical
  apply lp.ext
  funext x
  simp only [reducedLeftRegular_apply, deltaOne, lp.coeFn_single]
  by_cases hx : x = g
  · subst x; simp
  · have hne : g⁻¹ * x ≠ 1 := by
      intro h
      apply hx
      calc x = g * (g⁻¹ * x) := by simp
        _ = g := by rw [h, mul_one]
    rw [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hx]

theorem reducedLeftRegularUnitaryHom_injective :
    Function.Injective (reducedLeftRegularUnitaryHom G) := by
  classical
  intro g h heq
  have hop : reducedLeftRegular G g = reducedLeftRegular G h := congrArg Subtype.val heq
  have hdelta := congrArg
    (fun T : ReducedGroupCStar G ↦
      (T : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)) hop
  rw [reducedLeftRegular_deltaOne, reducedLeftRegular_deltaOne] at hdelta
  by_contra hgh
  have hx := congrArg (fun f : GroupHilbert G ↦ f g) hdelta
  change Pi.single g 1 g = Pi.single h 1 g at hx
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hgh] at hx
  exact one_ne_zero hx

/-- Exact unitary restriction of a proposed faithful reduced-C⋆ corona embedding. -/
structure FaithfulReducedCoronaUnitaryRestriction where
  I : Type
  U : Ultrafilter I
  X : I → FiniteModel
  map : unitary (ReducedGroupCStar G) →* UniversalWeakMF U X
  injective : Function.Injective map

namespace FaithfulReducedCoronaUnitaryRestriction

def groupRepresentation (D : FaithfulReducedCoronaUnitaryRestriction G) :
    G →* UniversalWeakMF D.U D.X :=
  D.map.comp (reducedLeftRegularUnitaryHom G)

theorem groupRepresentation_injective (D : FaithfulReducedCoronaUnitaryRestriction G) :
    Function.Injective D.groupRepresentation :=
  D.injective.comp (reducedLeftRegularUnitaryHom_injective G)

theorem false_of_mem_normMFResidual (D : FaithfulReducedCoronaUnitaryRestriction G)
    {g : G} (hg : g ∈ normMFResidual G) (hg1 : g ≠ 1) : False := by
  apply hg1
  apply D.groupRepresentation_injective
  rw [map_eq_one_of_mem_normMFResidual D.U D.X D.groupRepresentation hg, map_one]

end FaithfulReducedCoronaUnitaryRestriction

theorem no_faithfulReducedCoronaUnitaryRestriction_of_residual_eq_top
    [Nontrivial G] (hres : normMFResidual G = ⊤) :
    IsEmpty (FaithfulReducedCoronaUnitaryRestriction G) := by
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  exact ⟨fun D ↦
    FaithfulReducedCoronaUnitaryRestriction.false_of_mem_normMFResidual
      G D (g := g) (by rw [hres]; exact Subgroup.mem_top g) hg⟩

end

end GroupApproximation
