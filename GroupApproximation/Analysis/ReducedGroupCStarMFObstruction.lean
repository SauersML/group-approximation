import GroupApproximation.Analysis.ReducedGroupCStarTrace
import GroupApproximation.Sofic.NormMFResidualDetector

/-!
# Reduced group C⋆-algebras and norm-matrix-corona obstructions

The repository's norm-matrix corona is presently formalized exactly at the
level of its unitary group.  We therefore do not invent an ambient algebra
quotient or a general C⋆-MF predicate.  Instead, this file records the minimal
restriction data that every faithful unital star-algebra embedding into such
a corona must provide: an injective homomorphism from the unitary group of the
concrete reduced group C⋆-algebra to `NormMatrixCoronaUnitary`.

Restricting this data further to the left regular unitaries gives a faithful
group corona representation.  Thus any nontrivial element in the norm-MF
residual obstructs the data, and a nontrivial group whose entire norm-MF
residual is full admits no faithful reduced-C⋆ embedding into a norm matrix
corona.
-/

namespace GroupApproximation

open ReducedGroupCStarTrace

noncomputable section

universe u

variable (G : Type u) [Group G]

/-- The left regular operator, bundled as an element of the concrete reduced
group C⋆-algebra. -/
def reducedLeftRegular (g : G) : ReducedGroupCStar G :=
  ⟨leftRegularOperator G g,
    StarSubalgebra.le_topologicalClosure _
      (StarAlgebra.subset_adjoin ℂ (Set.range (leftRegularOperator G))
        ⟨g, rfl⟩)⟩

@[simp]
theorem reducedLeftRegular_coe (g : G) :
    (reducedLeftRegular G g : GroupHilbert G →L[ℂ] GroupHilbert G) =
      leftRegularOperator G g :=
  rfl

@[simp]
theorem reducedLeftRegular_apply (g : G) (f : GroupHilbert G) (x : G) :
    (reducedLeftRegular G g : GroupHilbert G →L[ℂ] GroupHilbert G) f x =
      f (g⁻¹ * x) :=
  rfl

/-- Left regular operators multiply according to the group law. -/
theorem reducedLeftRegular_mul (g h : G) :
    reducedLeftRegular G (g * h) =
      reducedLeftRegular G g * reducedLeftRegular G h := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext x
  simp only [Subalgebra.coe_mul, reducedLeftRegular_apply]
  rw [mul_inv_rev, mul_assoc]

@[simp]
theorem reducedLeftRegular_one : reducedLeftRegular G 1 = 1 := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext x
  simp only [reducedLeftRegular_apply, inv_one, one_mul, Subalgebra.coe_one,
    ContinuousLinearMap.one_apply]

/-- The adjoint of a left regular operator is the inverse translation. -/
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
  rfl

/-- A left regular group element is a unitary in the reduced group
C⋆-algebra. -/
def reducedLeftRegularUnitary (g : G) : unitary (ReducedGroupCStar G) :=
  ⟨reducedLeftRegular G g, by
    rw [star_reducedLeftRegular, ← reducedLeftRegular_mul, inv_mul,
      reducedLeftRegular_one]⟩

/-- The left regular representation into the unitary group of the concrete
reduced group C⋆-algebra. -/
def reducedLeftRegularUnitaryHom : G →* unitary (ReducedGroupCStar G) where
  toFun := reducedLeftRegularUnitary G
  map_one' := by
    apply Subtype.ext
    exact reducedLeftRegular_one G
  map_mul' g h := by
    apply Subtype.ext
    exact reducedLeftRegular_mul G g h

/-- Left regular unitaries move the identity point mass to their labelled
point masses. -/
theorem reducedLeftRegular_deltaOne (g : G) :
    (reducedLeftRegular G g : GroupHilbert G →L[ℂ] GroupHilbert G)
      (deltaOne G) = lp.single 2 g 1 := by
  apply lp.ext
  funext x
  simp only [reducedLeftRegular_apply, deltaOne, lp.coeFn_single]
  by_cases hx : x = g
  · subst x
    simp
  · have hne : g⁻¹ * x ≠ 1 := by
      intro h
      apply hx
      calc
        x = g * (g⁻¹ * x) := by simp
        _ = g := by rw [h, mul_one]
    simp [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hx]

/-- The left regular representation is faithful. -/
theorem reducedLeftRegularUnitaryHom_injective :
    Function.Injective (reducedLeftRegularUnitaryHom G) := by
  intro g h heq
  have hop : reducedLeftRegular G g = reducedLeftRegular G h :=
    congrArg Subtype.val heq
  have hdelta := DFunLike.congr_fun (congrArg Subtype.val hop) (deltaOne G)
  rw [reducedLeftRegular_deltaOne, reducedLeftRegular_deltaOne] at hdelta
  by_contra hgh
  have := DFunLike.congr_fun (congrArg DFunLike.coe hdelta) g
  simpa [lp.coeFn_single, Pi.single_eq_same, Pi.single_eq_of_ne hgh.symm] using this

/-- The exact unitary restriction furnished by a faithful unital star-algebra
embedding of `C*ᵣ(G)` into a norm matrix corona.  Since the ambient algebra
corona has not been constructed in this repository, this structure neither
pretends to be nor asserts such a construction; it records precisely the
faithful restriction consumed by the obstruction. -/
structure FaithfulReducedCoronaUnitaryRestriction where
  /-- The finite matrix sizes of the corona. -/
  X : ℕ → FiniteModel
  /-- Restriction of the proposed faithful algebra embedding to unitaries. -/
  map : unitary (ReducedGroupCStar G) →* NormMatrixCoronaUnitary X
  /-- Faithfulness remains visible on the unitary group. -/
  injective : Function.Injective map

namespace FaithfulReducedCoronaUnitaryRestriction

/-- Restricting faithful reduced-C⋆ corona data to the left regular unitaries
produces a group corona representation. -/
def groupRepresentation (D : FaithfulReducedCoronaUnitaryRestriction G) :
    G →* NormMatrixCoronaUnitary D.X :=
  D.map.comp (reducedLeftRegularUnitaryHom G)

/-- The induced group corona representation is faithful. -/
theorem groupRepresentation_injective
    (D : FaithfulReducedCoronaUnitaryRestriction G) :
    Function.Injective D.groupRepresentation :=
  D.injective.comp (reducedLeftRegularUnitaryHom_injective G)

/-- A nontrivial norm-MF-residual element rules out faithful reduced-C⋆
unitary restriction data. -/
theorem false_of_mem_normMFResidual
    (D : FaithfulReducedCoronaUnitaryRestriction G)
    {g : G} (hg : g ∈ normMFResidual G) (hg1 : g ≠ 1) : False := by
  apply hg1
  apply D.groupRepresentation_injective
  rw [map_eq_one_of_mem_normMFResidual D.X D.groupRepresentation hg, map_one]

end FaithfulReducedCoronaUnitaryRestriction

/-- If the norm-MF residual is the whole nontrivial group, no faithful
reduced-C⋆ unitary restriction to any norm matrix corona exists. -/
theorem no_faithfulReducedCoronaUnitaryRestriction_of_residual_eq_top
    [Nontrivial G] (hres : normMFResidual G = ⊤) :
    IsEmpty (FaithfulReducedCoronaUnitaryRestriction G) := by
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  exact ⟨fun D ↦ D.false_of_mem_normMFResidual
    (hres ▸ Subgroup.mem_top g) hg⟩

end


end GroupApproximation
